#!/usr/bin/env pwsh
<#
PRE-1 builder replay. This script changes only the exact registered source
fragment, then runs the layered builder firewall, builds the builder closure
producer targets and elaborates the typed builder consumer. It does not touch
the frozen contract registry or its runner; it checks that they are unchanged.
Run StartupOnly, then one OnlyCase, before full mode.
#>
[CmdletBinding()]
param(
  [AllowEmptyString()][string]$OnlyCase,
  [switch]$StartupOnly,
  [switch]$SelectorProbeOnly,
  [switch]$SelectorBoundarySelfTestOnly,
  [switch]$RegistrySelfTestOnly,
  [switch]$DeadlineSelfTestOnly,
  # Evidence (contract lane, this host, 2026-09-12): per-stage maxima were under
  # 25 s and a cold contract build took 77.2 s. The builder closure is larger, so
  # 600 s gives more than 2x margin over any observed stage.
  [ValidateRange(1, 86400)][int]$DeadlineSeconds = 600,
  # Selector-boundary child stages peaked at 16.9 s; 2x plus shell startup.
  [ValidateRange(1, 300)][int]$AdministrativeDeadlineSeconds = 120,
  # The contract default of 12 s FAILED on this host (shell startup measured
  # 8.997 s); 30 s passed; the PRE-1-A1 audit used 45 s.
  [ValidateRange(1, 120)][int]$SleeperDeadlineSeconds = 45,
  [ValidateRange(1024, 1073741824)][int]$OutputLimitBytes = 16777216,
  # Validator stage (stage S8): the compiled `rmq_preprocessing_validate`
  # executable's full fixture run and each negative control. Revised on the
  # measured run recorded in BUILDER_STAGE_LOG.md.
  [ValidateRange(1, 86400)][int]$ValidatorDeadlineSeconds = 1800,
  [string]$LakePath = '',
  [string]$EvidenceDirectory = '.lake/preprocessing-builder-replay'
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$script:SelectorWasBound = $PSBoundParameters.ContainsKey('OnlyCase')
$script:RepositoryRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$script:Utf8 = [Text.UTF8Encoding]::new($false, $true)
$script:RegistryPath = Join-Path $script:RepositoryRoot 'docs/internal/extensions/pre1/builder_cases.json'
# Registry order. When cases are appended, add their IDs here in registry order
# and recompute the pin below.
$script:ExpectedIds = @(
  'B01_FIREWALL_IMPORT', 'B02_CLOSURE_BYTES', 'B03_LAYERED_CONTRACT_GUARD',
  'B04_HEADERFIRST_WEAKEN', 'B05_TAIL_WEAKEN', 'B06_WORD_MISSING_WEAKEN',
  'B07_COMPARISON_MISSING_WEAKEN', 'B08_WORD_RECEIPT_WEAKEN', 'B09_COMPARISON_RECEIPT_WEAKEN',
  'B10_EXTENT_SIBLING', 'B11_EXTENT_DELETE', 'B12_ACCEPT_COMMENT', 'B13_TOY_PIN_DRIFT',
  'B14_HEADERFIRST_CONSUMER', 'B15_ARRAYRUN_FINAL_WEAKEN',
  'B16_PROGRAM_PARAMETER', 'B17_PROGRAMWORD_PARAMETER', 'B18_EFFICIENTBUILD_RELOCATION',
  'B19_L_KEY_NUMERAL', 'B20_L_WORD_NUMERAL', 'B21_B_NUMERAL', 'B22_BPRIME_NUMERAL',
  'B23_P0_NUMERAL', 'B24_P1_NUMERAL', 'B25_P2_NUMERAL', 'B26_P3_NUMERAL', 'B27_P4_NUMERAL',
  'B28_P5_NUMERAL', 'B29_P6_NUMERAL', 'B30_P7_NUMERAL', 'B31_P8_NUMERAL', 'B32_P9_NUMERAL',
  'B33_D_NUMERAL', 'B34_C_NUMERAL',
  'B35_COMPILE_REALIZES_WEAKEN', 'B36_COMPILE_SAFE_WEAKEN', 'B37_RUN_WRITE_AT_WEAKEN',
  'B38_RUN_LOAD_AT_WEAKEN', 'B39_WRITES_REPLAY_SIBLING', 'B40_RUN_AGREE_KEYS_WEAKEN',
  'B41_FUEL_EXTENSION_WEAKEN', 'B42_SAFETY_SHIFT_ARM_WEAKEN', 'B43_CARTESIAN_QUADRATIC_RESCAN',
  'B44_PROGRAM_SEMANTIC_IMPORT', 'B45_RUNFACTS_WORK_WEAKEN', 'B46_RUNFACTS_WORKSPACE_CW_WEAKEN',
  'B47_RUNFACTS_WORKSPACE_DW_WEAKEN', 'B48_RUNFACTS_NOINPUTWRITES_WEAKEN', 'B49_RUNFACTS_REGISTERBANK_WEAKEN',
  'B50_CAPSTONE_CW_NUMERAL', 'B51_CAPSTONE_DW_NUMERAL', 'B52_CAPSTONE_ACCEPT_COMMENT',
  'B53_RUNFACTS_HALTS_WEAKEN', 'B54_RUNFACTS_HALTS_FUEL_LARGER', 'B55_RUN_SAFE_LENGTH_WEAKEN'
)
# Registry version. Version 2 (repair PRE-1-R2) appends B53-B55 and makes a
# consumer-stage rejection also require the profile's marker to be absent.
$script:ExpectedRegistryVersion = 2
# Frozen independently of parsed contents. Only Git's CRLF/LF transport is
# normalized for this pin; raw file hashes remain in the evidence/restoration.
# Recompute from the repository root (CRLF->LF, lowercase hex):
#   $u=[Text.UTF8Encoding]::new($false,$true); $t=$u.GetString([IO.File]::ReadAllBytes('docs/internal/extensions/pre1/builder_cases.json')).Replace("`r`n","`n"); [BitConverter]::ToString([Security.Cryptography.SHA256]::Create().ComputeHash($u.GetBytes($t))).Replace('-','').ToLowerInvariant()
$script:ExpectedRegistrySha256 = '3e27e7626f4af805820071777246d3a5c2ac101e7adbb3db028219b2f46ae495'
# Producer stage: `lake build` of these targets, sequentially, LEAN_NUM_THREADS=1.
# HeaderUse is the consumer outside the closure; it must still build.
# Proof.Constants (stage S7) builds Builder.Program and the literal pins of the
# program constants that the consumer's V3-1..V3-6 section imports. It does not
# import the stage proof tower, so a closure mutation rebuilds only these pins.
$script:ProducerTargets = @(
  'RMQ.Core.WordRAM.Construction.Loop',
  'RMQ.Core.WordRAM.Construction.ArrayRun',
  'RMQ.Core.WordRAM.Construction.HeaderUse',
  'RMQ.Core.WordRAM.Construction.Proof.Constants'
)
$script:ConsumerScript = 'scripts/preprocessing_builder_check.lean'
# Stage S8: a case selects one compile profile. `builder` (the default) builds
# the closure targets above and elaborates the builder typed consumer;
# `capstone` builds the capstone and elaborates its typed consumer
# `RMQ/Validation/PreprocessingContract.lean`; `stackpass` builds the stack-pass
# stage proofs (the quadratic-mutation control of V2-7.6 is rejected there).
# Consumer rejections pin the exact failing line set of the profile's consumer.
$script:Profiles = [ordered]@{
  builder = [pscustomobject]@{
    Name = 'builder'; Targets = @($script:ProducerTargets); Consumer = $script:ConsumerScript
    SurfaceFile = 'preprocessing_builder_check.lean'; Marker = 'PRE1-BUILDER-TYPED-CONSUMERS PASS' }
  capstone = [pscustomobject]@{
    Name = 'capstone'; Targets = @('RMQ.Core.WordRAM.Construction.Capstone')
    Consumer = 'RMQ/Validation/PreprocessingContract.lean'
    SurfaceFile = 'PreprocessingContract.lean'; Marker = 'PRE1-CAPSTONE-TYPED-CONSUMERS PASS' }
  stackpass = [pscustomobject]@{
    Name = 'stackpass'; Targets = @('RMQ.Core.WordRAM.Construction.Proof.StackPass'); Consumer = $script:ConsumerScript
    SurfaceFile = 'preprocessing_builder_check.lean'; Marker = 'PRE1-BUILDER-TYPED-CONSUMERS PASS' }
}
$script:ValidatorScript = 'RMQ/Validation/Preprocessing.lean'
$script:ValidatorExe = 'rmq_preprocessing_validate'
# Negative controls of the validator and the message each must fail with.
$script:ValidatorNegatives = [ordered]@{
  'N01-MISSING-HEADER' = 'N01-MISSING-HEADER comparison: builder did not halt'
  'N02-WRONG-EXPECTED' = 'N02-WRONG-EXPECTED comparison: emitted cells differ from the expected allocation'
  'N03-MISMATCHED-ALLOCATION' = 'N03-MISMATCHED-ALLOCATION comparison: emitted cells differ from the expected allocation'
  'N04-WRITE-UNIT-CONFUSION' = 'N04-WRITE-UNIT-CONFUSION comparison: emitted cells differ from the expected allocation'
}
$script:BuilderManifestRelative = 'docs/internal/extensions/pre1/builder_manifest.json'
# Condition C3 (audit PRE-1-A1C P2-4): a case may carry `"manifest": "rehash"`.
# Only these closure modules are hashed in the builder manifest AND open to the
# registry; for such a case the runner re-hashes exactly that manifest entry to
# the mutant's normalized SHA-256 for the duration of the case and restores the
# manifest bytes with the source, so the mutation reaches the producer and
# consumer stages while the committed manifest never changes.
$script:RehashablePaths = @(
  'RMQ/Core/WordRAM/Construction/Program.lean',
  'RMQ/Core/WordRAM/Construction/Calculus.lean',
  'RMQ/Core/WordRAM/Construction/Safety.lean',
  'RMQ/Core/WordRAM/Construction/Structured.lean',
  'RMQ/Core/WordRAM/Construction/Compiler.lean',
  'RMQ/Core/WordRAM/Construction/Loop.lean',
  'RMQ/Core/WordRAM/Construction/ArrayRun.lean',
  'RMQ/Core/WordRAM/Construction/Builder/Program.lean',
  'RMQ/Core/WordRAM/Construction/Builder/Cartesian.lean'
)
# CONTRACT.md V3-1 relocation: a case may carry one `companion` edit
# ({path, before, after}) applied and restored together with its primary edit,
# so a declaration can move from the program host module into a consumer-side
# module in one mutation. Only these consumer-side modules may take one; they
# are outside the builder closure and are not manifest-hashed.
$script:CompanionPaths = @(
  'RMQ/Core/WordRAM/Construction/Proof/Constants.lean'
)
# Frozen contract surfaces (registry v1 and its runner). Normalized CRLF->LF,
# lowercase hex, computed 2026-09-12 at c1c970b. A change here is a change to
# the frozen contract lane and must be made deliberately.
$script:FrozenContractSurfaces = [ordered]@{
  'docs/internal/extensions/pre1/contract_cases.json' = 'aaec37a62bc74b483d09362a5d16f62afc2ae3a7be007577bc13e4c87c98574e'
  'scripts/preprocessing_contract_firewall.ps1' = '1f6903d5ae753fb49ac0d21611ba82aeb61fe9c8aced63e2c6469473b5f28786'
  'scripts/preprocessing_contract_replay.ps1' = 'b85ff767098d3a3249a86b78d2e9e96e63d7822dd82a3752fac933479cf5424c'
  'docs/internal/extensions/pre1/primitive_manifest.json' = 'a1d31f0bc4b1d732a331d4bac3b1b2103e3be9812fd0b1eb2e9769c45931fcfa'
}
$script:StageResults = [Collections.Generic.List[object]]::new()
$script:CaseResults = [Collections.Generic.List[object]]::new()
$script:SelfTestResults = [Collections.Generic.List[object]]::new()
$script:EvidenceRoot = ''
$script:Report = $null

function Get-ByteHash([byte[]]$Bytes) {
  $sha = [Security.Cryptography.SHA256]::Create()
  try { return ([BitConverter]::ToString($sha.ComputeHash($Bytes))).Replace('-', '').ToLowerInvariant() }
  finally { $sha.Dispose() }
}

function Get-FileHashExact([string]$Path) {
  return Get-ByteHash ([IO.File]::ReadAllBytes($Path))
}

function Get-NormalizedContentHash([byte[]]$Bytes) {
  $text = $script:Utf8.GetString($Bytes).Replace("`r`n", "`n")
  return Get-ByteHash ($script:Utf8.GetBytes($text))
}

function Save-Json([string]$Name, [object]$Value) {
  [IO.File]::WriteAllText((Join-Path $script:EvidenceRoot $Name),
    ($Value | ConvertTo-Json -Depth 30), $script:Utf8)
}

function Assert-FrozenContractSurfaces {
  foreach ($relative in $script:FrozenContractSurfaces.Keys) {
    $observed = Get-NormalizedContentHash ([IO.File]::ReadAllBytes((Join-Path $script:RepositoryRoot $relative)))
    if ($observed -cne $script:FrozenContractSurfaces[$relative]) {
      throw "PRE-BUILDER-FROZEN: contract surface changed: $relative"
    }
  }
}

function Assert-Registry([object]$Registry, [string]$ObservedHash) {
  if ($null -eq $Registry -or $null -eq $Registry.PSObject.Properties['version'] -or
      $Registry.version -cne $script:ExpectedRegistryVersion -or $null -eq $Registry.PSObject.Properties['cases']) {
    throw "PRE-REGISTRY: expected version=$($script:ExpectedRegistryVersion) and cases"
  }
  $cases = @($Registry.cases)
  if ($cases.Count -eq 0 -or $cases.Count -ne $script:ExpectedIds.Count) {
    throw 'PRE-REGISTRY: nonempty exact registry count required'
  }
  $seen = [Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  for ($i = 0; $i -lt $cases.Count; $i += 1) {
    $case = $cases[$i]
    foreach ($field in @('id', 'kind', 'path', 'before', 'after', 'expected', 'expectedStage', 'expectedSurface')) {
      if ($null -eq $case.PSObject.Properties[$field] -or $case.$field -isnot [string]) {
        throw "PRE-REGISTRY: missing or non-string field $field at index $i"
      }
    }
    if (-not $seen.Add($case.id) -or $case.id -cne $script:ExpectedIds[$i]) {
      throw "PRE-REGISTRY: duplicate, missing, unexpected or reordered ID at index $i"
    }
    if ($case.kind -cnotin @('mutation', 'control') -or
        $case.expected -cnotin @('reject', 'accept') -or
        $case.expectedStage -cnotin @('firewall', 'producer', 'consumer') -or
        [string]::IsNullOrWhiteSpace($case.before) -or
        $case.before -ceq $case.after -or
        [string]::IsNullOrWhiteSpace($case.expectedSurface)) {
      throw "PRE-REGISTRY: malformed case $($case.id)"
    }
    if (($case.kind -ceq 'mutation' -and $case.expected -cne 'reject') -or
        ($case.kind -ceq 'control' -and $case.expected -cne 'accept')) {
      throw "PRE-REGISTRY: kind/verdict mismatch for $($case.id)"
    }
    $profileName = 'builder'
    if ($null -ne $case.PSObject.Properties['profile']) {
      if ($case.profile -isnot [string] -or -not $script:Profiles.Contains([string]$case.profile) -or
          $case.profile -ceq 'builder') {
        throw "PRE-REGISTRY: profile must be omitted or one of capstone, stackpass: $($case.id)"
      }
      $profileName = [string]$case.profile
    }
    $surfaceFile = [regex]::Escape($script:Profiles[$profileName].SurfaceFile)
    # A consumer rejection pins the exact SET of failing consumer lines: one or
    # more space-separated `<consumer file>:<line>:` items of the case's profile.
    if ($case.expected -ceq 'reject' -and $case.expectedStage -ceq 'consumer' -and
        $case.expectedSurface -cnotmatch ('^' + $surfaceFile + ':[1-9][0-9]*:( ' + $surfaceFile + ':[1-9][0-9]*:)*$')) {
      throw "PRE-REGISTRY: consumer rejection must pin filename and exact line set: $($case.id)"
    }
    if ($null -ne $case.PSObject.Properties['manifest']) {
      if ($case.manifest -isnot [string] -or $case.manifest -cne 'rehash' -or
          $case.path -cnotin $script:RehashablePaths -or $case.expectedStage -ceq 'firewall') {
        throw "PRE-REGISTRY: manifest re-hash must be 'rehash' on a hashed closure module outside the firewall stage: $($case.id)"
      }
    }
    if ($null -ne $case.PSObject.Properties['companion']) {
      $companion = $case.companion
      if ($null -eq $companion -or $companion -is [string] -or $companion -is [array]) {
        throw "PRE-REGISTRY: companion must be one object: $($case.id)"
      }
      foreach ($field in @('path', 'before', 'after')) {
        if ($null -eq $companion.PSObject.Properties[$field] -or $companion.$field -isnot [string]) {
          throw "PRE-REGISTRY: missing or non-string companion field $field for $($case.id)"
        }
      }
      if ($companion.path -cnotin $script:CompanionPaths -or $companion.path -ceq $case.path -or
          $case.kind -cne 'mutation' -or [string]::IsNullOrWhiteSpace($companion.before) -or
          $companion.before -ceq $companion.after) {
        throw "PRE-REGISTRY: malformed companion edit for $($case.id)"
      }
    }
    # A closed path set prevents the data registry from mutating any other lane.
    if ($case.path -cnotin @(
        'RMQ/Core/WordRAM/Construction/Program.lean',
        'RMQ/Core/WordRAM/Construction/Calculus.lean',
        'RMQ/Core/WordRAM/Construction/Safety.lean',
        'RMQ/Core/WordRAM/Construction/Structured.lean',
        'RMQ/Core/WordRAM/Construction/Compiler.lean',
        'RMQ/Core/WordRAM/Construction/Loop.lean',
        'RMQ/Core/WordRAM/Construction/ArrayRun.lean',
        'RMQ/Core/WordRAM/Construction/Builder/Program.lean',
        'RMQ/Core/WordRAM/Construction/Builder/Cartesian.lean',
        'RMQ/Core/WordRAM/Construction/Proof/RunFacts.lean',
        'RMQ/Core/WordRAM/Construction/Capstone.lean',
        'RMQ/Validation/PreprocessingContract.lean',
        'RMQ/Core/WordRAM/Construction/HeaderUse.lean',
        'RMQ/Core/WordRAM/Construction/Primitive.lean',
        'scripts/preprocessing_builder_check.lean')) {
      throw "PRE-REGISTRY: mutation path is outside the PRE builder surface: $($case.path)"
    }
  }
  if ($ObservedHash -cne $script:ExpectedRegistrySha256) {
    throw "PRE-REGISTRY: frozen SHA-256 mismatch: $ObservedHash"
  }
}

function Select-Cases([object[]]$Cases) {
  if (-not $script:SelectorWasBound) { return @($Cases) }
  if ([string]::IsNullOrWhiteSpace($OnlyCase)) { throw 'PRE-SELECTOR: explicitly empty or whitespace selector' }
  if ($OnlyCase -cnotmatch '^B[0-9]{2}_[A-Z][A-Z0-9_]*$') { throw 'PRE-SELECTOR: malformed selector' }
  $selected = @($Cases | Where-Object { $_.id -ceq $OnlyCase })
  if ($selected.Count -ne 1) { throw 'PRE-SELECTOR: unknown selector' }
  return $selected
}

function Invoke-Stage([string]$Stage, [string]$FilePath, [string[]]$Arguments,
    [int]$Seconds = $DeadlineSeconds, [hashtable]$Environment = @{}) {
  $result = Invoke-RMQOwnedBoundedProcess -FilePath $FilePath -Arguments $Arguments `
    -WorkingDirectory $script:RepositoryRoot -Stage $Stage -DeadlineSeconds $Seconds `
    -OutputLimitBytes $OutputLimitBytes -TempRoot (Join-Path $script:EvidenceRoot 'process') `
    -Environment $Environment
  $entry = [pscustomobject][ordered]@{
    command = $FilePath; arguments = @($Arguments); environment = $Environment
    platform = [Environment]::OSVersion.ToString(); powershell = $PSVersionTable.PSVersion.ToString()
    result = $result
  }
  $script:StageResults.Add($entry)
  Save-Json ('stage-' + ('{0:D3}' -f $script:StageResults.Count) + '.json') $entry
  return $result
}

function Assert-Completed([object]$Result) {
  if ($Result.TimedOut -or $Result.OutputLimitExceeded) {
    throw "PRE-PROCESS: inconclusive $($Result.Stage); timeout=$($Result.TimedOut), outputLimit=$($Result.OutputLimitExceeded)"
  }
}

function Assert-Success([object]$Result) {
  Assert-Completed $Result
  if ($Result.ExitCode -ne 0) {
    throw "PRE-PROCESS: $($Result.Stage) exited $($Result.ExitCode): $($Result.Output -join ' | ')"
  }
}

function Get-CaseProfile([object]$Case) {
  if ($null -ne $Case -and $null -ne $Case.PSObject.Properties['profile']) { return $script:Profiles[[string]$Case.profile] }
  return $script:Profiles['builder']
}

function Invoke-Compile([string]$Prefix, [object]$Profile = $script:Profiles['builder']) {
  $results = [Collections.Generic.List[object]]::new()
  # The layered builder firewall runs the contract guard itself as a child.
  $firewall = Invoke-Stage "$Prefix-firewall" (Get-Process -Id $PID).Path `
    @('-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass', '-File',
      (Join-Path $PSScriptRoot 'preprocessing_builder_firewall.ps1')) `
    -Seconds $AdministrativeDeadlineSeconds
  $results.Add($firewall)
  Assert-Completed $firewall
  if ($firewall.ExitCode -ne 0) { return @($results) }
  # This pinned Lake version has no -j option. The environment constrains Lean
  # worker threads; producer/consumer invocations are sequential in this runner.
  $producer = Invoke-Stage "$Prefix-producer" $script:LakePath `
    (@('build') + @($Profile.Targets)) `
    -Environment @{ LEAN_NUM_THREADS = '1' }
  $results.Add($producer)
  Assert-Completed $producer
  if ($producer.ExitCode -eq 0) {
    $consumer = Invoke-Stage "$Prefix-consumer" $script:LakePath `
      @('env', 'lean', $Profile.Consumer) `
      -Environment @{ LEAN_NUM_THREADS = '1' }
    $results.Add($consumer)
    Assert-Completed $consumer
  }
  return @($results)
}

function Resolve-PinnedLake([string]$ExplicitPath) {
  if (-not [string]::IsNullOrWhiteSpace($ExplicitPath)) {
    $resolved = if ([IO.Path]::IsPathRooted($ExplicitPath)) {
      [IO.Path]::GetFullPath($ExplicitPath)
    } else { [IO.Path]::GetFullPath((Join-Path $script:RepositoryRoot $ExplicitPath)) }
  } else {
    # Avoid the elan proxy: it can attempt a network installation rather than
    # execute the already installed pinned compiler on a restricted host.
    $toolchain = [IO.File]::ReadAllText((Join-Path $script:RepositoryRoot 'lean-toolchain')).Trim()
    $elanRoot = [Environment]::GetEnvironmentVariable('ELAN_HOME')
    if ([string]::IsNullOrWhiteSpace($elanRoot)) {
      $elanRoot = Join-Path ([Environment]::GetFolderPath('UserProfile')) '.elan'
    }
    $directoryName = $toolchain.Replace('/', '--').Replace(':', '---')
    $binaryName = if (Test-RMQOwnedProcessWindows) { 'lake.exe' } else { 'lake' }
    $resolved = Join-Path (Join-Path (Join-Path $elanRoot 'toolchains') $directoryName) ('bin/' + $binaryName)
  }
  if (-not (Test-Path -LiteralPath $resolved -PathType Leaf)) {
    throw "PRE-TOOLCHAIN: installed pinned Lake unavailable at $resolved; supply -LakePath to the installed actual binary"
  }
  return [IO.Path]::GetFullPath($resolved)
}

function Read-Git([string[]]$Arguments, [string]$Label) {
  $result = Invoke-Stage $Label $script:GitPath (@('-c', 'core.excludesfile=') + @($Arguments)) `
    -Seconds $AdministrativeDeadlineSeconds
  Assert-Success $result
  return @($result.StandardOutput) -join "`n"
}

function Get-State([string]$Label) {
  return [pscustomobject][ordered]@{
    head = Read-Git @('rev-parse', 'HEAD') "$Label-head"
    status = Read-Git @('status', '--porcelain=v1', '--untracked-files=all') "$Label-status"
    worktree = Read-Git @('diff', '--binary', '--no-ext-diff') "$Label-worktree"
    index = Read-Git @('diff', '--cached', '--binary', '--no-ext-diff') "$Label-index"
  }
}

function Assert-State([object]$Before, [object]$After) {
  foreach ($field in @('head', 'status', 'worktree', 'index')) {
    if ($Before.$field -cne $After.$field) { throw "PRE-RESTORE: repository $field changed" }
  }
}

function Assert-SourceHashes {
  foreach ($source in $script:Report.sourceHashes) {
    if ((Get-FileHashExact (Join-Path $script:RepositoryRoot $source.path)) -cne $source.sha256) {
      throw "PRE-RESTORE: source changed: $($source.path)"
    }
  }
  if ((Get-FileHashExact $script:RegistryPath) -cne $script:Report.registrySha256) {
    throw 'PRE-RESTORE: raw registry bytes changed'
  }
}

# R2: the SET of failing consumer lines must EQUAL the registered set. Lines
# are taken only from `<file>:<line>:<col>: error` locations; warnings and bare
# substrings do not count. Duplicates collapse; order is irrelevant.
function Get-ConsumerErrorLines([string]$Output, [string]$SurfaceFile = 'preprocessing_builder_check.lean') {
  return @([regex]::Matches($Output, ([regex]::Escape($SurfaceFile) + ':(\d+):\d+: error')) |
    ForEach-Object { [int]$_.Groups[1].Value } | Sort-Object -Unique)
}

function Get-ExpectedConsumerLines([string]$Surface, [string]$SurfaceFile = 'preprocessing_builder_check.lean') {
  return @([regex]::Matches($Surface, ([regex]::Escape($SurfaceFile) + ':(\d+):')) |
    ForEach-Object { [int]$_.Groups[1].Value } | Sort-Object -Unique)
}

function Test-LineSetEquality([int[]]$Observed, [int[]]$Expected) {
  if ($Observed.Count -eq 0 -or $Observed.Count -ne $Expected.Count) { return $false }
  for ($i = 0; $i -lt $Observed.Count; $i += 1) {
    if ($Observed[$i] -ne $Expected[$i]) { return $false }
  }
  return $true
}

function Test-CaseVerdict([object]$Case, [object[]]$Results) {
  $stages = @('firewall', 'producer', 'consumer')
  if ($Results.Count -eq 0 -or $Results.Count -gt $stages.Count) { return $false }
  for ($i = 0; $i -lt $Results.Count; $i += 1) {
    if ($Results[$i].Stage -cne "$($Case.id)-$($stages[$i])" -or
        $Results[$i].TimedOut -or $Results[$i].OutputLimitExceeded) { return $false }
  }
  $expectedIndex = [Array]::IndexOf($stages, [string]$Case.expectedStage)
  if ($expectedIndex -lt 0) { return $false }
  # The expected stage's output is read only after the stage-count checks, so a
  # run that stopped at an earlier stage is a plain FAIL, not an index error.
  if ($Case.expected -ceq 'accept') {
    if ($Results.Count -ne 3 -or @($Results | Where-Object { $_.ExitCode -ne 0 }).Count -ne 0) {
      return $false
    }
    $output = $Results[$expectedIndex].Output -join "`n"
    return $output.Contains($Case.expectedSurface)
  } elseif ($Case.expected -ceq 'reject') {
    if ($Results.Count -ne ($expectedIndex + 1) -or $Results[$expectedIndex].ExitCode -eq 0) {
      return $false
    }
    for ($i = 0; $i -lt $expectedIndex; $i += 1) {
      if ($Results[$i].ExitCode -ne 0) { return $false }
    }
    $output = $Results[$expectedIndex].Output -join "`n"
    if ($Case.expectedStage -ceq 'consumer') {
      $caseProfile = Get-CaseProfile $Case
      # Registry version 2 (repair PRE-1-R2, audit PRE-1-A2 P2-1): a rejected
      # consumer must not print its profile's verdict marker.
      if ($output.Contains($caseProfile.Marker)) { return $false }
      $surfaceFile = $caseProfile.SurfaceFile
      return (Test-LineSetEquality @(Get-ConsumerErrorLines $output $surfaceFile) @(Get-ExpectedConsumerLines $Case.expectedSurface $surfaceFile))
    }
    # Firewall and producer rejections pin one diagnostic line or location.
    return $output.Contains($Case.expectedSurface)
  }
  return $false
}

function New-MatcherStage([string]$Stage, [int]$Exit, [string]$Output, [bool]$TimedOut = $false) {
  return [pscustomobject]@{
    Stage = "T00_MATCHER-$Stage"; ExitCode = $Exit; Output = @($Output)
    TimedOut = $TimedOut; OutputLimitExceeded = $false
  }
}

function Invoke-MatcherTests {
  $reject = [pscustomobject]@{
    id = 'T00_MATCHER'; expected = 'reject'; expectedStage = 'consumer'
    expectedSurface = 'preprocessing_builder_check.lean:42:'
  }
  $rejectSet = [pscustomobject]@{
    id = 'T00_MATCHER'; expected = 'reject'; expectedStage = 'consumer'
    expectedSurface = 'preprocessing_builder_check.lean:42: preprocessing_builder_check.lean:57:'
  }
  $rejectFirewall = [pscustomobject]@{
    id = 'T00_MATCHER'; expected = 'reject'; expectedStage = 'firewall'
    expectedSurface = 'PRE1-BUILDER-FIREWALL imports rejected: RMQ/Core/WordRAM/Construction/Program.lean'
  }
  $rejectProducer = [pscustomobject]@{
    id = 'T00_MATCHER'; expected = 'reject'; expectedStage = 'producer'
    expectedSurface = 'RMQ/Core/WordRAM/Construction/HeaderUse.lean:12:'
  }
  $accept = [pscustomobject]@{
    id = 'T00_MATCHER'; expected = 'accept'; expectedStage = 'consumer'
    expectedSurface = 'PRE1-BUILDER-TYPED-CONSUMERS PASS'
  }
  $rejectCapstone = [pscustomobject]@{
    id = 'T00_MATCHER'; expected = 'reject'; expectedStage = 'consumer'; profile = 'capstone'
    expectedSurface = 'PreprocessingContract.lean:227: PreprocessingContract.lean:349:'
  }
  $prefix = @((New-MatcherStage 'firewall' 0 ''), (New-MatcherStage 'producer' 0 ''))
  $e42 = 'scripts/preprocessing_builder_check.lean:42:7: error: mismatch'
  $e43 = 'scripts/preprocessing_builder_check.lean:43:7: error: mismatch'
  $e57 = 'scripts/preprocessing_builder_check.lean:57:3: error: mismatch'
  $c227 = 'RMQ/Validation/PreprocessingContract.lean:227:2: error: type mismatch'
  $c349 = 'RMQ/Validation/PreprocessingContract.lean:349:2: error: type mismatch'
  $fixtures = @(
    @{ id='rejection-without-marker'; case=$reject; expected=$true; stages=@($prefix) + @((New-MatcherStage 'consumer' 1 "$e42`nsome other output")) },
    @{ id='rejection-with-marker'; case=$reject; expected=$false; stages=@($prefix) + @((New-MatcherStage 'consumer' 1 "$e42`nPRE1-BUILDER-TYPED-CONSUMERS PASS")) },
    @{ id='capstone-rejection-without-marker'; case=$rejectCapstone; expected=$true; stages=@($prefix) + @((New-MatcherStage 'consumer' 1 "$c349`n$c227")) },
    @{ id='capstone-rejection-with-marker'; case=$rejectCapstone; expected=$false; stages=@($prefix) + @((New-MatcherStage 'consumer' 1 "$c227`n$c349`nPRE1-CAPSTONE-TYPED-CONSUMERS PASS")) },
    @{ id='exact-rejection'; case=$reject; expected=$true; stages=@($prefix) + @((New-MatcherStage 'consumer' 1 $e42)) },
    @{ id='exact-set-rejection'; case=$rejectSet; expected=$true; stages=@($prefix) + @((New-MatcherStage 'consumer' 1 "$e57`n$e42")) },
    @{ id='missing-expected-line'; case=$rejectSet; expected=$false; stages=@($prefix) + @((New-MatcherStage 'consumer' 1 $e42)) },
    @{ id='extra-failing-line'; case=$reject; expected=$false; stages=@($prefix) + @((New-MatcherStage 'consumer' 1 "$e42`n$e43")) },
    @{ id='duplicate-line-collapses'; case=$reject; expected=$true; stages=@($prefix) + @((New-MatcherStage 'consumer' 1 "$e42`nscripts/preprocessing_builder_check.lean:42:12: error: second")) },
    @{ id='wrong-stage'; case=$reject; expected=$false; stages=@((New-MatcherStage 'firewall' 0 ''), (New-MatcherStage 'producer' 1 $e42)) },
    @{ id='wrong-location'; case=$reject; expected=$false; stages=@($prefix) + @((New-MatcherStage 'consumer' 1 $e43)) },
    @{ id='generic-substring-only'; case=$reject; expected=$false; stages=@($prefix) + @((New-MatcherStage 'consumer' 1 'preprocessing_builder_check.lean:42: builderContract_holds.steps')) },
    @{ id='unrelated-error-plus-generic-substring'; case=$reject; expected=$false; stages=@($prefix) + @((New-MatcherStage 'consumer' 1 "$e43`npreprocessing_builder_check.lean:42: builderContract_holds.steps")) },
    @{ id='warning-is-not-error'; case=$reject; expected=$false; stages=@($prefix) + @((New-MatcherStage 'consumer' 1 'scripts/preprocessing_builder_check.lean:42:7: warning: unused')) },
    @{ id='timeout-is-inconclusive'; case=$reject; expected=$false; stages=@($prefix) + @((New-MatcherStage 'consumer' -1 $e42 $true)) },
    @{ id='success-is-not-rejection'; case=$reject; expected=$false; stages=@($prefix) + @((New-MatcherStage 'consumer' 0 $e42)) },
    @{ id='exact-acceptance'; case=$accept; expected=$true; stages=@($prefix) + @((New-MatcherStage 'consumer' 0 'PRE1-BUILDER-TYPED-CONSUMERS PASS')) },
    @{ id='acceptance-at-wrong-stage'; case=$accept; expected=$false; stages=@((New-MatcherStage 'firewall' 0 'PRE1-BUILDER-TYPED-CONSUMERS PASS'), (New-MatcherStage 'producer' 0 ''), (New-MatcherStage 'consumer' 0 '')) },
    @{ id='firewall-rejection'; case=$rejectFirewall; expected=$true; stages=@((New-MatcherStage 'firewall' 1 'PRE1-BUILDER-FIREWALL imports rejected: RMQ/Core/WordRAM/Construction/Program.lean actual=[RMQ.Core.WordRAM.Construction.Model,RMQ.Core.Shape]')) },
    @{ id='firewall-rejection-wrong-surface'; case=$rejectFirewall; expected=$false; stages=@((New-MatcherStage 'firewall' 1 'PRE1-BUILDER-FIREWALL closure module missing: RMQ/Core/WordRAM/Construction/Program.lean')) },
    @{ id='firewall-rejection-at-producer'; case=$rejectFirewall; expected=$false; stages=@((New-MatcherStage 'firewall' 0 ''), (New-MatcherStage 'producer' 1 'PRE1-BUILDER-FIREWALL imports rejected: RMQ/Core/WordRAM/Construction/Program.lean')) },
    @{ id='producer-rejection'; case=$rejectProducer; expected=$true; stages=@((New-MatcherStage 'firewall' 0 ''), (New-MatcherStage 'producer' 1 'RMQ/Core/WordRAM/Construction/HeaderUse.lean:12:5: error: unknown identifier')) },
    @{ id='producer-rejection-at-consumer'; case=$rejectProducer; expected=$false; stages=@($prefix) + @((New-MatcherStage 'consumer' 1 'RMQ/Core/WordRAM/Construction/HeaderUse.lean:12:5: error: unknown identifier')) }
  )
  foreach ($fixture in $fixtures) {
    $observed = Test-CaseVerdict $fixture.case @($fixture.stages)
    if ($observed -ne $fixture.expected) { throw "PRE-SELFTEST: production verdict matcher $($fixture.id) returned $observed" }
    $script:SelfTestResults.Add([pscustomobject]@{
      category = 'matcher'; case = $fixture.id; expected = $fixture.expected; observed = $observed; verdict = 'PASS'
    })
  }
}

function Invoke-RegistryTests([object]$Registry, [string]$Hash) {
  $tests = @('empty', 'missing', 'extra', 'duplicate', 'reordered', 'version', 'hash',
    'consumer-surface-column', 'consumer-surface-prefixed', 'consumer-surface-empty-item',
    'path-outside', 'stage', 'manifest-value', 'manifest-unhashed-path', 'manifest-firewall-stage',
    'companion-path-outside', 'companion-same-path', 'companion-noop', 'companion-missing-field',
    'profile-unknown', 'profile-explicit-builder', 'profile-surface-mismatch')
  foreach ($test in $tests) {
    $copy = ($Registry | ConvertTo-Json -Depth 20) | ConvertFrom-Json
    $testHash = $Hash
    switch ($test) {
      'empty' { $copy.cases = @() }
      'missing' { $copy.cases = @($copy.cases | Select-Object -Skip 1) }
      'extra' { $copy.cases = @($copy.cases) + @($copy.cases[0]) }
      'duplicate' { $copy.cases[1] = $copy.cases[0] }
      'reordered' { $first = $copy.cases[0]; $copy.cases[0] = $copy.cases[1]; $copy.cases[1] = $first }
      'version' { $copy.version = 1 }
      'hash' { $testHash = 'invalid' }
      'consumer-surface-column' { $copy.cases[0].expectedStage = 'consumer'; $copy.cases[0].expectedSurface = 'preprocessing_builder_check.lean:42:7:' }
      'consumer-surface-prefixed' { $copy.cases[0].expectedStage = 'consumer'; $copy.cases[0].expectedSurface = 'scripts/preprocessing_builder_check.lean:42:' }
      'consumer-surface-empty-item' { $copy.cases[0].expectedStage = 'consumer'; $copy.cases[0].expectedSurface = 'preprocessing_builder_check.lean:42:  preprocessing_builder_check.lean:57:' }
      'path-outside' { $copy.cases[0].path = 'RMQ/Core/WordRAM/Construction/Contract.lean' }
      'stage' { $copy.cases[0].expectedStage = 'builder' }
      'manifest-value' {
        $copy.cases[0].expectedStage = 'consumer'
        $copy.cases[0].expectedSurface = 'preprocessing_builder_check.lean:42:'
        $copy.cases[0] | Add-Member -NotePropertyName manifest -NotePropertyValue 'yes' -Force
      }
      'manifest-unhashed-path' {
        $copy.cases[3] | Add-Member -NotePropertyName manifest -NotePropertyValue 'rehash' -Force
      }
      'manifest-firewall-stage' {
        $copy.cases[0] | Add-Member -NotePropertyName manifest -NotePropertyValue 'rehash' -Force
      }
      'companion-path-outside' {
        $copy.cases[0] | Add-Member -NotePropertyName companion -NotePropertyValue ([pscustomobject]@{
          path = 'RMQ/Core/WordRAM/Construction/Proof/Exact.lean'; before = 'x'; after = 'y' }) -Force
      }
      'companion-same-path' {
        $copy.cases[0] | Add-Member -NotePropertyName companion -NotePropertyValue ([pscustomobject]@{
          path = $copy.cases[0].path; before = 'x'; after = 'y' }) -Force
      }
      'companion-noop' {
        $copy.cases[0] | Add-Member -NotePropertyName companion -NotePropertyValue ([pscustomobject]@{
          path = 'RMQ/Core/WordRAM/Construction/Proof/Constants.lean'; before = 'x'; after = 'x' }) -Force
      }
      'profile-unknown' {
        $copy.cases[0] | Add-Member -NotePropertyName profile -NotePropertyValue 'tower' -Force
      }
      'profile-explicit-builder' {
        $copy.cases[0] | Add-Member -NotePropertyName profile -NotePropertyValue 'builder' -Force
      }
      'profile-surface-mismatch' {
        $copy.cases[4].expectedStage = 'consumer'
        $copy.cases[4].expectedSurface = 'preprocessing_builder_check.lean:42:'
        $copy.cases[4] | Add-Member -NotePropertyName profile -NotePropertyValue 'capstone' -Force
      }
      'companion-missing-field' {
        $copy.cases[0] | Add-Member -NotePropertyName companion -NotePropertyValue ([pscustomobject]@{
          path = 'RMQ/Core/WordRAM/Construction/Proof/Constants.lean'; before = 'x' }) -Force
      }
    }
    $rejected = $false
    try { Assert-Registry $copy $testHash }
    catch { if ($_.Exception.Message.StartsWith('PRE-REGISTRY:')) { $rejected = $true } else { throw } }
    if (-not $rejected) { throw "PRE-SELFTEST: registry $test accepted" }
    $script:SelfTestResults.Add([pscustomobject]@{ category = 'registry'; case = $test; verdict = 'PASS' })
  }
  # Positive control: the set-valued consumer surface shape itself is accepted
  # by the validator (the hash is the caller's; only the shape rule is under test).
  $copy = ($Registry | ConvertTo-Json -Depth 20) | ConvertFrom-Json
  $copy.cases[0].expectedStage = 'consumer'
  $copy.cases[0].expectedSurface = 'preprocessing_builder_check.lean:42: preprocessing_builder_check.lean:57:'
  Assert-Registry $copy $Hash
  $script:SelfTestResults.Add([pscustomobject]@{ category = 'registry'; case = 'consumer-surface-set-accepted'; verdict = 'PASS' })
  Invoke-MatcherTests
}

function Invoke-SelectorBoundaryTests {
  # A child PowerShell script invokes the actual public parameter boundary.
  # Literal '' survives both PowerShell 5 and 7; a native argv empty argument
  # may not, so relying on native forwarding would not test bound-empty state.
  $targetLiteral = (Join-Path $PSScriptRoot 'preprocessing_builder_replay.ps1').Replace("'", "''")
  $wrapper = Join-Path $script:EvidenceRoot 'selector-boundary.ps1'
  $body = @'
param([string]$BoundaryCase, [string]$EvidenceRoot)
$ErrorActionPreference = 'Stop'
$ErrorView = 'NormalView'
$target = '__TARGET__'
switch ($BoundaryCase) {
  'omitted' { & $target -SelectorProbeOnly -EvidenceDirectory $EvidenceRoot }
  'valid' { & $target -SelectorProbeOnly -EvidenceDirectory $EvidenceRoot -OnlyCase 'B01_FIREWALL_IMPORT' }
  'empty' { & $target -SelectorProbeOnly -EvidenceDirectory $EvidenceRoot -OnlyCase '' }
  'whitespace' { & $target -SelectorProbeOnly -EvidenceDirectory $EvidenceRoot -OnlyCase ' ' }
  'malformed' { & $target -SelectorProbeOnly -EvidenceDirectory $EvidenceRoot -OnlyCase 'B01_FIREWALL_IMPORT,B02_CLOSURE_BYTES' }
  'unknown' { & $target -SelectorProbeOnly -EvidenceDirectory $EvidenceRoot -OnlyCase 'B99_UNKNOWN' }
  'zero' { & $target -SelectorProbeOnly -EvidenceDirectory $EvidenceRoot -OnlyCase '0' }
  'missing' { & $target -SelectorProbeOnly -EvidenceDirectory $EvidenceRoot -OnlyCase }
  'duplicate' { & $target -SelectorProbeOnly -EvidenceDirectory $EvidenceRoot -OnlyCase 'B01_FIREWALL_IMPORT' -OnlyCase 'B02_CLOSURE_BYTES' }
  default { throw 'unknown boundary fixture' }
}
exit $LASTEXITCODE
'@
  [IO.File]::WriteAllText($wrapper, $body.Replace('__TARGET__', $targetLiteral), $script:Utf8)
  $shell = (Get-Process -Id $PID).Path
  foreach ($test in @('omitted', 'valid', 'empty', 'whitespace', 'malformed', 'unknown', 'zero', 'missing', 'duplicate')) {
    $result = Invoke-Stage "selector-$test" $shell `
      @('-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', $wrapper,
        '-BoundaryCase', $test, '-EvidenceRoot', $script:EvidenceRoot) `
      -Seconds $AdministrativeDeadlineSeconds
    Assert-Completed $result
    $positive = $test -cin @('omitted', 'valid')
    $output = $result.Output -join "`n"
    if ($positive) {
      $expectedCount = if ($test -ceq 'omitted') { $script:ExpectedIds.Count } else { 1 }
      $expectedIds = if ($test -ceq 'omitted') { $script:ExpectedIds -join ',' } else { 'B01_FIREWALL_IMPORT' }
      if ($result.ExitCode -ne 0 -or -not $output.Contains("PRE-BUILDER-SELECTOR-PROBE: selected=$expectedCount ids=$expectedIds")) {
        throw "PRE-SELFTEST: selector $test did not select $expectedCount"
      }
    } elseif ($result.ExitCode -eq 0 -or $output.Contains('PRE-BUILDER-SELECTOR-PROBE:')) {
      throw "PRE-SELFTEST: selector $test was not rejected at script boundary"
    } else {
      $surface = switch ($test) {
        'empty' { 'PRE-SELECTOR: explicitly empty or whitespace selector' }
        'whitespace' { 'PRE-SELECTOR: explicitly empty or whitespace selector' }
        'malformed' { 'PRE-SELECTOR: malformed selector' }
        'unknown' { 'PRE-SELECTOR: unknown selector' }
        'zero' { 'PRE-SELECTOR: malformed selector' }
        'missing' { 'MissingArgument' }
        'duplicate' { 'ParameterAlreadyBound' }
      }
      if (-not $output.Contains($surface)) { throw "PRE-SELFTEST: selector $test failed outside its pinned surface $surface" }
    }
    $script:SelfTestResults.Add([pscustomobject]@{ category = 'selector'; case = $test; verdict = 'PASS'; exit = $result.ExitCode })
  }
}

function Invoke-DeadlineTests {
  Invoke-RMQOwnedProcessDeterministicTests
  Invoke-RMQOwnedProcessCollectionSelfTest
  $script:SelfTestResults.Add([pscustomobject]@{
    category = 'deadline'; case = 'deterministic-plans-and-collections'; verdict = 'PASS'
    scope = 'Production launch-plan branches and process-ID collection logic; foreign-host execution is not implied'
  })
  $shell = (Get-Process -Id $PID).Path
  $failurePath = Join-Path $script:EvidenceRoot 'known-failure.ps1'
  [IO.File]::WriteAllText($failurePath, "[Console]::Error.WriteLine('PRE-EXPECTED-STDERR'); exit 23", $script:Utf8)
  $failed = Invoke-Stage 'known-failure' $shell @('-NoLogo', '-NoProfile', '-File', $failurePath) `
    -Seconds $AdministrativeDeadlineSeconds
  Assert-Completed $failed
  if ($failed.ExitCode -ne 23 -or -not (@($failed.StandardError) -join "`n").Contains('PRE-EXPECTED-STDERR')) {
    throw 'PRE-SELFTEST: exit/stderr preservation failed'
  }
  $script:SelfTestResults.Add([pscustomobject]@{ category = 'deadline'; case = 'exit-stderr'; verdict = 'PASS' })
  $sleeper = Join-Path $script:EvidenceRoot 'owned-sleeper.ps1'
  $pidFile = Join-Path $script:EvidenceRoot 'owned-descendant.pid'
  $body = @'
$shell = (Get-Process -Id $PID).Path
$options = @{ FilePath = $shell; ArgumentList = @('-NoLogo', '-NoProfile', '-Command', 'Start-Sleep -Seconds 120'); PassThru = $true }
if ([Environment]::OSVersion.Platform -eq [PlatformID]::Win32NT) { $options.WindowStyle = 'Hidden' }
$child = Start-Process @options
[IO.File]::WriteAllText('__PIDFILE__', [string]$child.Id)
Start-Sleep -Seconds 120
'@
  [IO.File]::WriteAllText($sleeper, $body.Replace('__PIDFILE__', $pidFile.Replace("'", "''")), $script:Utf8)
  $timed = Invoke-Stage 'owned-descendant-timeout' $shell @('-NoLogo', '-NoProfile', '-File', $sleeper) `
    -Seconds $SleeperDeadlineSeconds
  if (-not $timed.TimedOut) { throw 'PRE-SELFTEST: sleeper did not reach timeout' }
  if (-not (Test-Path -LiteralPath $pidFile -PathType Leaf)) {
    throw 'PRE-SELFTEST: INCONCLUSIVE descendant did not start; this host condition is uncovered'
  }
  $childId = [int][IO.File]::ReadAllText($pidFile)
  if (@(Get-RMQAliveProcessIds @($childId)).Count -ne 0) {
    throw "PRE-SELFTEST: owned descendant $childId survived"
  }
  $script:SelfTestResults.Add([pscustomobject]@{
    category = 'deadline'; case = 'owned-descendant'; verdict = 'PASS'; descendant = $childId
    platform = [Environment]::OSVersion.ToString(); ownership = $timed.Ownership
    unexecutedHost = if (Test-RMQOwnedProcessWindows) { 'POSIX execution not covered by this run' } else { 'Windows execution not covered by this run' }
  })
}

function Invoke-Validator {
  # The compiled executable is built through Lake (`lake build <exe>`), then
  # run in full mode and once per negative control through its selector
  # channel; each negative must fail with its pinned message.
  $build = Invoke-Stage 'validator-build' $script:LakePath @('build', $script:ValidatorExe) `
    -Seconds $ValidatorDeadlineSeconds -Environment @{ LEAN_NUM_THREADS = '1' }
  Assert-Success $build
  $full = Invoke-Stage 'validator-full' $script:LakePath @('exe', $script:ValidatorExe) `
    -Seconds $ValidatorDeadlineSeconds -Environment @{ LEAN_NUM_THREADS = '1' }
  Assert-Success $full
  $fullOutput = $full.Output -join "`n"
  if (-not $fullOutput.Contains('PRE1-VALIDATE PASS cases=') -or -not $fullOutput.Contains(' mode=full')) {
    throw 'PRE-VALIDATOR: full fixture run did not print its PASS marker'
  }
  $negatives = [Collections.Generic.List[object]]::new()
  foreach ($id in $script:ValidatorNegatives.Keys) {
    $run = Invoke-Stage "validator-$id" $script:LakePath @('exe', $script:ValidatorExe) `
      -Seconds $ValidatorDeadlineSeconds -Environment @{ LEAN_NUM_THREADS = '1'; PRE1_VALIDATE_SELECTOR = "id:$id" }
    Assert-Completed $run
    $output = $run.Output -join "`n"
    if ($run.ExitCode -eq 0 -or -not $output.Contains($script:ValidatorNegatives[$id]) -or
        $output.Contains('PRE1-VALIDATE PASS')) {
      throw "PRE-VALIDATOR: negative control $id did not fail with its pinned message"
    }
    $negatives.Add([pscustomobject]@{ id = $id; exit = $run.ExitCode; verdict = 'REJECTED-AS-EXPECTED' })
  }
  return [pscustomobject]@{ full = 'PASS'; negatives = @($negatives) }
}

function New-FragmentMutation([string]$Id, [string]$RelativePath, [string]$Before, [string]$After) {
  $path = Join-Path $script:RepositoryRoot $RelativePath
  $original = [IO.File]::ReadAllBytes($path)
  $text = $script:Utf8.GetString($original)
  $sourceWithoutCrlf = $text.Replace("`r`n", '')
  if ($sourceWithoutCrlf.Contains("`r") -or
      ($text.Contains("`r`n") -and $sourceWithoutCrlf.Contains("`n"))) {
    throw "PRE-MUTATION: $Id source $RelativePath has unsupported mixed line endings"
  }
  $needle = $Before.Replace("`r`n", "`n")
  $replacement = $After.Replace("`r`n", "`n")
  if ($text.Contains("`r`n")) {
    $needle = $needle.Replace("`n", "`r`n")
    $replacement = $replacement.Replace("`n", "`r`n")
  }
  $at = $text.IndexOf($needle, [StringComparison]::Ordinal)
  if ($at -lt 0 -or $text.IndexOf($needle, $at + $needle.Length, [StringComparison]::Ordinal) -ge 0) {
    throw "PRE-MUTATION: $Id before fragment must occur exactly once in $RelativePath"
  }
  return [pscustomobject]@{
    Path = $path; Original = $original
    Mutant = $text.Substring(0, $at) + $replacement + $text.Substring($at + $needle.Length)
  }
}

function Invoke-Case([object]$Case, [object]$InitialState, [string]$RegistryHash) {
  $primary = New-FragmentMutation $Case.id $Case.path $Case.before $Case.after
  $path = $primary.Path
  $original = $primary.Original
  $beforeHash = Get-ByteHash $original
  $mutant = $primary.Mutant
  $companion = $null
  if ($null -ne $Case.PSObject.Properties['companion']) {
    $companion = New-FragmentMutation $Case.id $Case.companion.path $Case.companion.before $Case.companion.after
  }
  $rehash = $null -ne $Case.PSObject.Properties['manifest']
  $manifestPath = Join-Path $script:RepositoryRoot $script:BuilderManifestRelative
  $manifestOriginal = $null
  $manifestMutant = $null
  if ($rehash) {
    # The committed manifest entry must hash the unmutated source; exactly that
    # entry's digest is replaced by the mutant's normalized digest.
    $manifestOriginal = [IO.File]::ReadAllBytes($manifestPath)
    $manifestText = $script:Utf8.GetString($manifestOriginal)
    $oldDigest = (Get-NormalizedContentHash $original).ToUpperInvariant()
    $newDigest = (Get-NormalizedContentHash ($script:Utf8.GetBytes($mutant))).ToUpperInvariant()
    $pattern = '("path":\s*"' + [regex]::Escape($Case.path) + '",\s*"sha256":\s*")' + $oldDigest + '"'
    $entryMatches = [regex]::Matches($manifestText, $pattern)
    if ($entryMatches.Count -ne 1) {
      throw "PRE-MUTATION: $($Case.id) manifest entry for $($Case.path) must hash the unmutated source exactly once"
    }
    $manifestMutant = [regex]::Replace($manifestText, $pattern, ('${1}' + $newDigest + '"'))
  }
  $entry = [ordered]@{
    id = $Case.id; expected = $Case.expected; expectedStage = $Case.expectedStage; expectedSurface = $Case.expectedSurface
    source = $Case.path; beforeSha256 = $beforeHash; mutationSha256 = Get-ByteHash ($script:Utf8.GetBytes($mutant))
    profile = (Get-CaseProfile $Case).Name
    manifest = if ($rehash) { 'rehash' } else { 'frozen' }
    manifestBeforeSha256 = if ($rehash) { Get-ByteHash $manifestOriginal } else { '' }
    manifestMutationSha256 = if ($rehash) { Get-ByteHash ($script:Utf8.GetBytes($manifestMutant)) } else { '' }
    manifestAfterSha256 = ''
    companionSource = if ($null -ne $companion) { $Case.companion.path } else { '' }
    companionBeforeSha256 = if ($null -ne $companion) { Get-ByteHash $companion.Original } else { '' }
    companionMutationSha256 = if ($null -ne $companion) { Get-ByteHash ($script:Utf8.GetBytes($companion.Mutant)) } else { '' }
    companionAfterSha256 = ''
    afterSha256 = ''; verdict = 'INCOMPLETE'; compile = @(); restoreCompile = @(); restoration = 'PENDING'; error = ''
  }
  try {
    if ($rehash) { [IO.File]::WriteAllBytes($manifestPath, $script:Utf8.GetBytes($manifestMutant)) }
    [IO.File]::WriteAllBytes($path, $script:Utf8.GetBytes($mutant))
    if ($null -ne $companion) { [IO.File]::WriteAllBytes($companion.Path, $script:Utf8.GetBytes($companion.Mutant)) }
    $entry.compile = @(Invoke-Compile $Case.id (Get-CaseProfile $Case))
    if (-not (Test-CaseVerdict $Case @($entry.compile))) {
      throw "PRE-MUTATION: $($Case.id) did not produce $($Case.expected) at exact stage=$($Case.expectedStage) surface=$($Case.expectedSurface)"
    }
    $entry.verdict = 'PASS'
  } catch {
    $entry.error = $_.Exception.Message
    $entry.verdict = 'FAIL'
    throw
  } finally {
    # Restoration happens even after failed compilation, timeout, or mismatch.
    [IO.File]::WriteAllBytes($path, $original)
    if ($null -ne $companion) { [IO.File]::WriteAllBytes($companion.Path, $companion.Original) }
    if ($rehash) { [IO.File]::WriteAllBytes($manifestPath, $manifestOriginal) }
    $entry.afterSha256 = Get-FileHashExact $path
    if ($null -ne $companion) { $entry.companionAfterSha256 = Get-FileHashExact $companion.Path }
    if ($rehash) { $entry.manifestAfterSha256 = Get-FileHashExact $manifestPath }
    try {
      if ($entry.afterSha256 -cne $beforeHash) { throw 'PRE-RESTORE: byte SHA-256 differs' }
      if ($null -ne $companion -and $entry.companionAfterSha256 -cne $entry.companionBeforeSha256) {
        throw 'PRE-RESTORE: companion byte SHA-256 differs'
      }
      if ($rehash -and $entry.manifestAfterSha256 -cne $entry.manifestBeforeSha256) {
        throw 'PRE-RESTORE: builder manifest byte SHA-256 differs'
      }
      if ((Get-FileHashExact $script:RegistryPath) -cne $RegistryHash) { throw 'PRE-RESTORE: registry changed during replay' }
      $entry.restoreCompile = @(Invoke-Compile "$($Case.id)-restored" (Get-CaseProfile $Case))
      foreach ($stage in $entry.restoreCompile) { Assert-Success $stage }
      if ($entry.restoreCompile.Count -ne 3) { throw 'PRE-RESTORE: firewall, producer and consumer restoration were not all checked' }
      Assert-SourceHashes
      Assert-State $InitialState (Get-State "$($Case.id)-restored")
      $entry.restoration = 'EXACT'
    } catch {
      $entry.verdict = 'FAIL'; $entry.restoration = 'FAIL'
      $entry.error = ($entry.error + ' | ' + $_.Exception.Message).Trim(' ', '|')
      throw
    } finally {
      $script:CaseResults.Add([pscustomobject]$entry)
      Save-Json ("case-$($Case.id).json") $entry
    }
  }
}

try {
  $exclusive = @($StartupOnly, $SelectorProbeOnly, $SelectorBoundarySelfTestOnly,
    $RegistrySelfTestOnly, $DeadlineSelfTestOnly) | Where-Object { $_ }
  if (@($exclusive).Count -gt 1 -or
      ($script:SelectorWasBound -and ($StartupOnly -or $SelectorBoundarySelfTestOnly -or $RegistrySelfTestOnly -or $DeadlineSelfTestOnly))) {
    throw 'PRE-MODE: incompatible modes or selector'
  }
  $registryBytes = [IO.File]::ReadAllBytes($script:RegistryPath)
  $registryHash = Get-ByteHash $registryBytes
  $registryContentHash = Get-NormalizedContentHash $registryBytes
  $registry = $script:Utf8.GetString($registryBytes) | ConvertFrom-Json
  Assert-Registry $registry $registryContentHash
  $selected = @(Select-Cases @($registry.cases))
  if ($SelectorProbeOnly) {
    Write-Host "PRE-BUILDER-SELECTOR-PROBE: selected=$($selected.Count) ids=$(@($selected | ForEach-Object { $_.id }) -join ',')"
    exit 0
  }
  $evidenceBase = if ([IO.Path]::IsPathRooted($EvidenceDirectory)) {
    [IO.Path]::GetFullPath($EvidenceDirectory)
  } else { [IO.Path]::GetFullPath((Join-Path $script:RepositoryRoot $EvidenceDirectory)) }
  $repoPrefix = $script:RepositoryRoot.TrimEnd('\', '/') + [IO.Path]::DirectorySeparatorChar
  $cacheRoot = [IO.Path]::GetFullPath((Join-Path $script:RepositoryRoot '.lake'))
  $cachePrefix = $cacheRoot.TrimEnd('\', '/') + [IO.Path]::DirectorySeparatorChar
  $withinRepository = $evidenceBase.Equals($script:RepositoryRoot, [StringComparison]::OrdinalIgnoreCase) -or
    $evidenceBase.StartsWith($repoPrefix, [StringComparison]::OrdinalIgnoreCase)
  $withinCache = $evidenceBase.Equals($cacheRoot, [StringComparison]::OrdinalIgnoreCase) -or
    $evidenceBase.StartsWith($cachePrefix, [StringComparison]::OrdinalIgnoreCase)
  if ($withinRepository -and -not $withinCache) {
    throw 'PRE-EVIDENCE: inside this repository, evidence must be under ignored .lake; copy final evidence after replay'
  }
  $script:EvidenceRoot = Join-Path $evidenceBase ((Get-Date -Format 'yyyyMMdd-HHmmss') + '-' + [Guid]::NewGuid().ToString('N'))
  [void](New-Item -ItemType Directory -Path $script:EvidenceRoot -Force)
  . (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
  $script:Report = [ordered]@{
    schemaVersion = 1; phase = 'BUILDER'; verdict = 'INCOMPLETE'; registrySha256 = $registryHash
    registryContentSha256 = $registryContentHash
    runnerSha256 = Get-FileHashExact (Join-Path $PSScriptRoot 'preprocessing_builder_replay.ps1')
    registryExpected = $script:ExpectedIds; selectedExpected = @($selected | ForEach-Object { $_.id })
    producerTargets = @($script:ProducerTargets); consumerScript = $script:ConsumerScript
    frozenContractSurfaces = @($script:FrozenContractSurfaces.Keys | ForEach-Object {
      [pscustomobject]@{ path = $_; sha256 = $script:FrozenContractSurfaces[$_] } })
    executed = @(); sourceHashes = @(); baseline = $null; restored = $null
    mode = if ($StartupOnly) { 'startup' } elseif ($SelectorBoundarySelfTestOnly) { 'selector-selftest' } elseif ($RegistrySelfTestOnly) { 'registry-selftest' } elseif ($DeadlineSelfTestOnly) { 'deadline-selftest' } elseif ($script:SelectorWasBound) { 'focused' } else { 'full' }
    platform = [Environment]::OSVersion.ToString(); powershell = $PSVersionTable.PSVersion.ToString()
    deadlineSeconds = $DeadlineSeconds; administrationDeadlineSeconds = $AdministrativeDeadlineSeconds
    sleeperDeadlineSeconds = $SleeperDeadlineSeconds
    validator = $null; cases = @(); selfTests = @(); stages = @(); error = ''
  }
  if ($SelectorBoundarySelfTestOnly) { Invoke-SelectorBoundaryTests }
  elseif ($RegistrySelfTestOnly) { Invoke-RegistryTests $registry $registryContentHash }
  elseif ($DeadlineSelfTestOnly) { Invoke-DeadlineTests }
  else {
    # Cheap regression in every Lean mode: contract registry v1, its runner,
    # its guard and its manifest are byte-for-byte (modulo CRLF) untouched.
    Assert-FrozenContractSurfaces
    $script:LakePath = Resolve-PinnedLake $LakePath
    $script:GitPath = Resolve-RMQScalarApplicationPath @(Get-Command git -CommandType Application -ErrorAction Stop) 'git'
    $script:Report.baseline = Get-State 'baseline'
    $constructionRoot = Join-Path $script:RepositoryRoot 'RMQ/Core/WordRAM/Construction'
    $constructionSources = @([IO.Directory]::EnumerateFiles($constructionRoot, '*.lean', [IO.SearchOption]::AllDirectories) |
      ForEach-Object { $_.Substring($script:RepositoryRoot.Length + 1).Replace('\', '/') })
    $sourcePaths = @(@($registry.cases | ForEach-Object { $_.path }) + $constructionSources +
      @('scripts/preprocessing_builder_replay.ps1', 'scripts/preprocessing_builder_firewall.ps1',
        'scripts/preprocessing_contract_firewall.ps1', $script:ConsumerScript,
        'RMQ/Validation/PreprocessingContract.lean', $script:ValidatorScript, 'lakefile.toml',
        'docs/internal/extensions/pre1/builder_manifest.json',
        'docs/internal/extensions/pre1/primitive_manifest.json',
        'lean-toolchain') |
      Sort-Object -Unique)
    $script:Report.sourceHashes = @($sourcePaths | ForEach-Object {
      [pscustomobject]@{ path = $_; sha256 = Get-FileHashExact (Join-Path $script:RepositoryRoot $_) }
    })
    if (-not $StartupOnly -and -not $script:SelectorWasBound) {
      Invoke-RegistryTests $registry $registryContentHash
      Invoke-SelectorBoundaryTests
      Invoke-DeadlineTests
    }
    $baselineCompile = @(Invoke-Compile 'baseline')
    foreach ($stage in $baselineCompile) { Assert-Success $stage }
    if ($baselineCompile.Count -ne 3) { throw 'PRE-BASELINE: firewall, producer and typed consumer must all pass' }
    $capstoneBaseline = @(Invoke-Compile 'baseline-capstone' $script:Profiles['capstone'])
    foreach ($stage in $capstoneBaseline) { Assert-Success $stage }
    if ($capstoneBaseline.Count -ne 3 -or
        -not (($capstoneBaseline[2].Output -join "`n").Contains($script:Profiles['capstone'].Marker))) {
      throw 'PRE-BASELINE: the capstone producer and its typed consumer must pass with the marker'
    }
    if (-not $StartupOnly -and -not $script:SelectorWasBound) {
      $script:Report.validator = Invoke-Validator
    }
    if (-not $StartupOnly) {
      foreach ($case in $selected) {
        Invoke-Case $case $script:Report.baseline $registryHash
        Write-Host "PRE-CASE: $($case.id) PASS, exact restoration verified"
      }
      $executed = @($script:CaseResults | ForEach-Object { $_.id })
      if (($executed -join ',') -cne ($script:Report.selectedExpected -join ',')) {
        throw 'PRE-REGISTRY: executed IDs differ from selected expected IDs'
      }
    }
    Assert-SourceHashes
    $script:Report.restored = Get-State 'final'
    Assert-State $script:Report.baseline $script:Report.restored
  }
  $script:Report.verdict = 'PASS'
} catch {
  if ($null -ne $script:Report) { $script:Report.verdict = 'FAIL'; $script:Report.error = $_.Exception.Message }
  Write-Host "PRE-BUILDER-REPLAY: FAIL $($_.Exception.Message)"
  exit 1
} finally {
  if ($null -ne $script:Report -and -not [string]::IsNullOrEmpty($script:EvidenceRoot)) {
    $script:Report.executed = @($script:CaseResults | ForEach-Object { $_.id })
    $script:Report.cases = @($script:CaseResults)
    $script:Report.selfTests = @($script:SelfTestResults)
    $script:Report.stages = @($script:StageResults)
    Save-Json 'report.json' $script:Report
  }
}
Write-Host "PRE-BUILDER-REPLAY: PASS mode=$($script:Report.mode) executed=$($script:CaseResults.Count) registry=$($script:ExpectedIds.Count) evidence=$script:EvidenceRoot"
exit 0
