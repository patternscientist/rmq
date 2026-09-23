#!/usr/bin/env pwsh
[CmdletBinding()]
param(
  [AllowEmptyString()][string]$OnlyCase,
  [string]$LeanPath = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe',
  [ValidateRange(30, 3600)][int]$StageDeadlineSeconds = 180,
  [ValidateRange(30, 21600)][int]$CampaignDeadlineSeconds = 10800,
  [switch]$PrepareOnly,
  [switch]$RegistrySelfTestOnly,
  [switch]$LibrarySelfTestOnly,
  [switch]$SelectorProbeOnly,
  [switch]$SelectorBoundarySelfTestOnly
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
$repoRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$onlyCaseBound = $PSBoundParameters.ContainsKey('OnlyCase')
$utf8 = [Text.UTF8Encoding]::new($false, $true)
$scriptPath = 'scripts/packed_optimized_certificate_replay.ps1'
$fieldPath = 'docs/internal/extensions/opt1/certificate-replay/FIELDS.json'
$registryPath = 'docs/internal/extensions/opt1/certificate-replay/REGISTRY.md'
$provenancePath = 'docs/internal/extensions/opt1/runtime-replay/evidence/full-runtime.json'
$provenanceSHA256 = 'a7eb5831a88a7431607d5fe1d7189318d41978391e0a10be3ed336c014563661'
$replayProfilePath = 'scripts/packed_optimized_replay_profile.ps1'
$sourceProfilePath = 'docs/internal/extensions/opt1/repair-r1/profile/SOURCE_PROFILE.json'
$buildReceiptPath = 'docs/internal/extensions/opt1/repair-r1/profile/BUILD_RECEIPT.json'
# Filled only from the completed, independently source-anchored canonical build.
# A live artifact or input never supplies its own expected digest.
$buildReceiptSHA256 = 'eed1ecee4a031a9c3cfcadea445307d8e15e70e732e6ffdd5b166d135292b64e'
$replayIdentity = $null
$certificatePath = 'RMQ/Core/WordRAM/Optimization/Certificate.lean'
$capstonePath = 'RMQ/Core/WordRAM/Optimization/Capstone.lean'
$consumerPath = 'RMQ/Core/WordRAM/Optimization/Consumers.lean'
$sourcePaths = @($certificatePath, $capstonePath, $consumerPath)
$privateArtifacts = @($sourcePaths | ForEach-Object { $_.Substring(0, $_.Length - 5) + '.olean' })
$version = 'opt1-certificate-replay-v3'
$frozenFieldsSHA256 = '0d1529c98d35b6ff2ac53d58d107f0a47ec8f5d263f51819c085827c055a63bb'
# Literal order frozen from the coordinator's v3 contract, never from a mutant.
$fieldNames = @(
  'allocationResidualLittleO', 'completeResidualLittleO', 'widthBounds', 'dataCapacity',
  'completeCapacity', 'memoryWordsFit', 'allocationAddressesFit', 'programFieldsFit',
  'budgetExact', 'programLength', 'encodedProgramLength', 'programReduction', 'emittedProgram',
  'originalExecutionBound', 'originalReducedFuel', 'arbitraryMemoryObservations',
  'completedExecution', 'adequateFuel', 'registerCount', 'scratchCount', 'unusedRegisters',
  'validInputs', 'natContract', 'leftmost', 'result', 'halt', 'invalidGuard', 'stepBound',
  'categoryPartition', 'finalStateFit', 'transitionSafety', 'prefixSafety', 'readWidth',
  'positionalReadBacking', 'orderedLogicalRefinement', 'logicalReadOnly',
  'suppliedMemoryAgreement', 'specResult', 'noFailedLoads')
$registry = @(
  [pscustomobject]@{ Id='A01-UNCHANGED'; Kind='unchanged'; Field=''; Verdict='ACCEPT' },
  [pscustomobject]@{ Id='A02-COMMENT'; Kind='comment'; Field=''; Verdict='ACCEPT' }
)
for ($index = 0; $index -lt $fieldNames.Count; $index++) {
  $number = ($index + 1).ToString('00')
  $registry += [pscustomobject]@{ Id="D$number-$($fieldNames[$index])"; Kind='delete'; Field=$fieldNames[$index]; Verdict='REJECT' }
  $registry += [pscustomobject]@{ Id="W$number-$($fieldNames[$index])"; Kind='weaken'; Field=$fieldNames[$index]; Verdict='REJECT' }
}
$artifactRoot = $null
$baseline = $null
$initialStatus = $null
$importBaseline = $null
$dependencySnapshot = $null
$exitCode = 0
$completion = $null
$stages = [Collections.Generic.List[object]]::new()
$clock = [Diagnostics.Stopwatch]::StartNew()

function Read-CSource([string]$Path) { return [IO.File]::ReadAllText((Join-Path $repoRoot $Path), $utf8) }
function Normalize-CNewlines([string]$Text) { return $Text.Replace("`r`n", "`n") }
function Get-CHash([byte[]]$Bytes) {
  $hasher = [Security.Cryptography.SHA256]::Create()
  try { return ([BitConverter]::ToString($hasher.ComputeHash($Bytes))).Replace('-', '').ToLowerInvariant() }
  finally { $hasher.Dispose() }
}
function Assert-CExact([string[]]$Actual, [string[]]$Expected, [string]$Label) {
  if ($Expected.Count -eq 0 -or $Actual.Count -ne $Expected.Count -or
      ($Actual -join "`n") -cne ($Expected -join "`n") -or
      @($Actual | Select-Object -Unique).Count -ne $Actual.Count) {
    throw "OPT1-CERT-REGISTRY: $Label missing, duplicate, extra, reordered or changed"
  }
}
function Get-CRegion([string]$Text, [string]$Kind) {
  $begin = "  -- OPT1-REPLAY-$Kind-BEGIN"
  $end = "  -- OPT1-REPLAY-$Kind-END"
  if ([regex]::Matches($Text, [regex]::Escape($begin)).Count -ne 1 -or
      [regex]::Matches($Text, [regex]::Escape($end)).Count -ne 1) { throw "OPT1-CERT-REGISTRY: missing/duplicate $Kind markers" }
  $start = $Text.IndexOf("`n", $Text.IndexOf($begin)) + 1
  $finish = $Text.IndexOf($end)
  if ($start -le 0 -or $finish -le $start) { throw 'OPT1-CERT-REGISTRY: reversed markers' }
  return [pscustomobject]@{ Start=$start; End=$finish; Text=$Text.Substring($start, $finish - $start) }
}
function Get-CEntries([string]$Text, [string]$Kind) {
  $region = Get-CRegion $Text $Kind
  $pattern = if ($Kind -ceq 'FIELDS') { '(?m)^  ([A-Za-z][A-Za-z0-9]*) :' } else { '(?m)^  ([A-Za-z][A-Za-z0-9]*)(?: [^\r\n]*?)? :=' }
  $entries = @([regex]::Matches($region.Text, $pattern))
  for ($index = 0; $index -lt $entries.Count; $index++) {
    $start = $region.Start + $entries[$index].Index
    $finish = if ($index + 1 -lt $entries.Count) { $region.Start + $entries[$index + 1].Index } else { $region.End }
    [pscustomobject]@{ Name=$entries[$index].Groups[1].Value; Start=$start; End=$finish; Text=$Text.Substring($start, $finish-$start) }
  }
}
function Assert-CRegistry([string[]]$IDs = @($registry.Id), [string]$Certificate = '', [string]$Consumer = '') {
  if ($fieldNames.Count -ne 39 -or $registry.Count -ne 80) { throw 'OPT1-CERT-REGISTRY: exact v3 count mismatch' }
  Assert-CExact $IDs @($registry.Id) 'case IDs'
  if ((Get-CHash ([IO.File]::ReadAllBytes((Join-Path $repoRoot $fieldPath)))) -cne $frozenFieldsSHA256) {
    throw 'OPT1-CERT-REGISTRY: frozen v3 expected-proposition bytes changed'
  }
  $fields = Read-CSource $fieldPath | ConvertFrom-Json
  if ($fields.Version -cne 'opt1-certificate-fields-v3' -or $fields.FieldCount -ne 39) { throw 'OPT1-CERT-REGISTRY: field contract version mismatch' }
  Assert-CExact @($fields.Fields.Name) $fieldNames 'frozen field names'
  Assert-CExact @($fields.MutationKinds) @('delete-field-and-initializer', 'weaken-field-to-True-and-initializer-to-trivial') 'mutation kinds'
  Assert-CExact @($fields.Controls) @('unaltered-canonical-producer-consumers', 'nonsemantic-comment-change') 'accept controls'
  $markdown = Read-CSource $registryPath
  if ([regex]::Matches($markdown, '(?m)^Version: `opt1-certificate-replay-v3`\. Exactly 80 cases: 78 rejects and two accepts\.\r?$').Count -ne 1) { throw 'OPT1-CERT-REGISTRY: Markdown version mismatch' }
  $rows = @([regex]::Matches($markdown, '(?m)^\| (D[0-9]{2}-[A-Za-z]+) \| (W[0-9]{2}-[A-Za-z]+) \| ([A-Za-z]+) \|\r?$') |
    ForEach-Object { $_.Groups[1].Value; $_.Groups[2].Value })
  Assert-CExact $rows @($registry | Where-Object { $_.Verdict -ceq 'REJECT' } | ForEach-Object { $_.Id }) 'Markdown cases'
  if ($Certificate -ceq '') { $Certificate = Read-CSource $certificatePath }
  if ($Consumer -ceq '') { $Consumer = Read-CSource $consumerPath }
  $entries = @(Get-CEntries $Certificate 'FIELDS')
  Assert-CExact @($entries.Name) $fieldNames 'producer fields'
  Assert-CExact @((Get-CEntries (Read-CSource $capstonePath) 'INITIALIZERS').Name) $fieldNames 'producer initializers'
  foreach ($entry in $fields.Fields) {
    $field = $entry.Name
    $expected = Normalize-CNewlines $entry.ExpectedType
    $declaration = @($entries | Where-Object { $_.Name -ceq $field })[0]
    $fieldType = (Normalize-CNewlines $declaration.Text).Substring(('  ' + $field + ' : ').Length).TrimEnd()
    if ($fieldType -cne $expected) { throw "OPT1-CERT-REGISTRY: producer type differs from frozen $field" }
    $genericPattern = '(?ms)^theorem ' + $field + '_expectedType \(certificate : CompactPackedQueryCapstone\) :\r?\n(.*?) :=\r?\n  certificate\.' + $field + '\r?$'
    $canonicalPattern = '(?ms)^theorem ' + $field + '_canonical :\r?\n(.*?) :=\r?\n  ' + $field + '_expectedType compactPackedQueryCapstone_holds\r?$'
    foreach ($pattern in @($genericPattern, $canonicalPattern)) {
      $matched = [regex]::Matches($Consumer, $pattern)
      if ($matched.Count -ne 1 -or (Normalize-CNewlines $matched[0].Groups[1].Value).TrimStart() -cne $expected) {
        throw "OPT1-CERT-REGISTRY: independent fixed consumer type/body differs for $field"
      }
    }
  }
}
function Get-CSelection {
  if (-not $onlyCaseBound) { return $registry }
  if ([string]::IsNullOrWhiteSpace($OnlyCase)) { throw 'OPT1-CERT-SELECTOR: explicitly empty selector' }
  if ($OnlyCase -cnotmatch '^[ADW][0-9]{2}-[A-Za-z][A-Za-z0-9-]*$') { throw 'OPT1-CERT-SELECTOR: malformed selector' }
  $selected = @($registry | Where-Object { $_.Id -ceq $OnlyCase })
  if ($selected.Count -ne 1) { throw "OPT1-CERT-SELECTOR: unknown selector $OnlyCase" }
  return $selected
}
function Write-CJson([string]$Path, [object]$Value) {
  [IO.File]::WriteAllText($Path, ($Value | ConvertTo-Json -Depth 12), $utf8)
}
function Invoke-CProcess([string]$Name, [string]$Executable, [string[]]$Arguments, [string]$Directory, [hashtable]$Environment = @{}) {
  $remaining = $CampaignDeadlineSeconds - [int][Math]::Ceiling($clock.Elapsed.TotalSeconds)
  if ($remaining -le 0) { throw 'OPT1-CERT-PROCESS: total campaign deadline reached before launch' }
  $deadline = [Math]::Min($StageDeadlineSeconds, $remaining)
  Write-Host "OPT1-CERT-STAGE $Name deadline=${deadline}s"
  $result = Invoke-RMQOwnedBoundedProcess -FilePath $Executable -Arguments $Arguments -WorkingDirectory $Directory `
    -Stage $Name -DeadlineSeconds $deadline -OutputLimitBytes 4194304 -TempRoot $artifactRoot -Environment $Environment
  $record = [ordered]@{ Name=$Name; Executable=$Executable; Arguments=@($Arguments); Directory=$Directory; Environment=$Environment; Result=$result }
  $stages.Add($record)
  Write-CJson (Join-Path $artifactRoot "$Name.json") $record
  [IO.File]::WriteAllLines((Join-Path $artifactRoot "$Name.stdout.log"), [string[]]$result.StandardOutput, $utf8)
  [IO.File]::WriteAllLines((Join-Path $artifactRoot "$Name.stderr.log"), [string[]]$result.StandardError, $utf8)
  if ($result.TimedOut -or $result.OutputLimitExceeded) { throw "OPT1-CERT-PROCESS: $Name incomplete timeout/output limit" }
  return $result
}
function Assert-CAccepted([object]$Result) {
  if ($Result.ExitCode -ne 0 -or @($Result.StandardError).Count -ne 0 -or
      ($Result.Output -join "`n") -match '(?m): error:|declaration uses .sorry.') {
    throw "OPT1-CERT-VERDICT: producer/accept control failed at $($Result.Stage) exit=$($Result.ExitCode)"
  }
}
function Assert-CRejected([object]$Result, [string]$Text, [object]$Case) {
  if ($Result.TimedOut -or $Result.OutputLimitExceeded -or $Result.ExitCode -ne 1) { throw 'OPT1-CERT-VERDICT: missing ordinary rejection exit' }
  $joined = $Result.Output -join "`n"
  if ($joined -match '(?m)^error:') {
    throw 'OPT1-CERT-VERDICT: unlocated error is not an exact field rejection'
  }
  if ($joined -match '(?m)^uncaught exception:') {
    throw 'OPT1-CERT-VERDICT: uncaught exception is not a compile-time field rejection'
  }
  if ($joined -match 'deep recursion|stack overflow|internal exception|interrupted|unknown module|object file.*does not exist|maximum.*(recursion|heartbeats)|out of memory') {
    throw 'OPT1-CERT-VERDICT: setup/resource failure is not a type rejection'
  }
  $pattern = '(?m)^theorem ' + [regex]::Escape($Case.Field) + '_expectedType\b'
  $matches = [regex]::Matches($Text, $pattern)
  if ($matches.Count -ne 1) { throw 'OPT1-CERT-VERDICT: consumer theorem missing/duplicate' }
  $start = ($Text.Substring(0, $matches[0].Index) -split "`n").Count
  $next = [regex]::Match($Text.Substring($matches[0].Index + $matches[0].Length), '(?m)^theorem ')
  $end = if ($next.Success) { ($Text.Substring(0, $matches[0].Index + $matches[0].Length + $next.Index) -split "`n").Count } else { ($Text -split "`n").Count + 1 }
  $errors = @([regex]::Matches($joined, '(?m)^([^\r\n]+):(\d+):\d+: error:([^\r\n]*)'))
  if ($errors.Count -eq 0) { throw 'OPT1-CERT-VERDICT: no located consumer diagnostic' }
  foreach ($errorRow in $errors) {
    $file = $errorRow.Groups[1].Value.Replace('\', '/')
    $line = [int]$errorRow.Groups[2].Value
    $message = $errorRow.Groups[3].Value.Trim()
    $allowed = if ($Case.Kind -ceq 'delete') { '^invalid field\b' } else { '^(application )?type mismatch\b' }
    if (-not $file.EndsWith($consumerPath, [StringComparison]::Ordinal) -or
        $line -lt $start -or $line -ge $end -or $message -notmatch $allowed) {
      throw "OPT1-CERT-VERDICT: rejection outside exact $($Case.Field)_expectedType/$($Case.Kind) surface"
    }
  }
  if (-not $joined.Contains($Case.Field)) { throw 'OPT1-CERT-VERDICT: diagnostic did not identify selected field' }
}
function Get-CMutatedText([string]$Text, [string]$Kind, [object]$Case) {
  if ($Case.Kind -ceq 'unchanged') { return $Text }
  if ($Case.Kind -ceq 'comment') {
    if ($Kind -ceq 'FIELDS') { return $Text + "`n-- OPT1 certificate replay nonsemantic comment control`n" }
    return $Text
  }
  $entries = @(Get-CEntries $Text $Kind | Where-Object { $_.Name -ceq $Case.Field })
  if ($entries.Count -ne 1) { throw 'OPT1-CERT-MUTATION: target entry missing/duplicate' }
  $entry = $entries[0]
  $replacement = ''
  if ($Case.Kind -ceq 'weaken') {
    $newline = if ($Text.Contains("`r`n")) { "`r`n" } else { "`n" }
    $replacement = if ($Kind -ceq 'FIELDS') { "  $($Case.Field) : True$newline" } else { "  $($Case.Field) := True.intro$newline" }
  }
  return $Text.Substring(0, $entry.Start) + $replacement + $Text.Substring($entry.End)
}
function Get-COriginalSnapshot {
  $snapshot = [ordered]@{}
  foreach ($path in @($sourcePaths + @($fieldPath, $registryPath, $scriptPath, $provenancePath,
      $replayProfilePath, $sourceProfilePath, $buildReceiptPath,
      'docs/internal/extensions/opt1/repair-r1/profile/BUILD_DRIVER.ps1',
      'RMQ/Validation/PackedOptimized.lean', 'lean-toolchain', 'lakefile.toml',
      'scripts/owned_process_tree.ps1', 'scripts/packed_optimized_runtime.ps1'))) {
    $snapshot[$path] = Get-CHash ([IO.File]::ReadAllBytes((Join-Path $repoRoot $path)))
  }
  return $snapshot
}
function Get-CTrackedStatus([string]$Phase) {
  $gitPath = Resolve-RMQScalarApplicationPath @(Get-Command git -CommandType Application) 'git'
  $result = Invoke-CProcess "tracked-source-status-$Phase" $gitPath (@('-c', 'core.excludesfile=', 'status', '--porcelain=v1', '--untracked-files=no', '--') + $sourcePaths + @($fieldPath)) $repoRoot
  Assert-CAccepted $result
  return @($result.StandardOutput) -join "`n"
}
function Get-CImportSnapshot {
  $shellPath = (Get-Process -Id $PID).Path
  $result = Invoke-CProcess 'import-freshness' $shellPath @('-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', (Join-Path $PSScriptRoot 'packed_optimized_runtime.ps1'), '-ArtifactCheckOnly') $repoRoot
  Assert-CAccepted $result
  $paths = @($result.StandardOutput | Where-Object { $_.StartsWith('OPT1-ARTIFACTS ', [StringComparison]::Ordinal) })
  if ($paths.Count -ne 1) { throw 'OPT1-CERT-IMPORT: expected one production import-manifest path' }
  $manifest = [IO.File]::ReadAllText((Join-Path $paths[0].Substring('OPT1-ARTIFACTS '.Length) 'imports-check.json'), $utf8) | ConvertFrom-Json
  if (@($manifest).Count -eq 0) { throw 'OPT1-CERT-IMPORT: empty production import snapshot' }
  if (@($manifest.Module | Select-Object -Unique).Count -ne @($manifest).Count -or
      @($manifest.Source | Select-Object -Unique).Count -ne @($manifest).Count -or
      @($manifest.Artifact | Select-Object -Unique).Count -ne @($manifest).Count) {
    throw 'OPT1-CERT-IMPORT: duplicate production import record'
  }
  $hashes = [ordered]@{}
  foreach ($entry in $manifest) {
    if ($entry.Module -cnotmatch '^RMQ(?:\.[A-Za-z_][A-Za-z0-9_]*)*$' -or
        $entry.Source -cne ($entry.Module.Replace('.', '/') + '.lean') -or
        $entry.Artifact -cne ('.lake/build/lib/lean/' + $entry.Module.Replace('.', '/') + '.olean')) {
      throw 'OPT1-CERT-IMPORT: production module/source/artifact mapping differs'
    }
    $hashes[$entry.Source] = $entry.SourceSHA256
    $hashes[$entry.Artifact] = $entry.ArtifactSHA256
  }
  Assert-CImportProvenance $hashes
  return $hashes
}
function Assert-CImportProvenance([object]$Hashes) {
  # The old receipt remains a byte-pinned historical record. Its undocumented
  # source serialization is not the expected identity for this new build.
  $bytes = [IO.File]::ReadAllBytes((Join-Path $repoRoot $provenancePath))
  if ((Get-CHash $bytes) -cne $provenanceSHA256) { throw 'OPT1-CERT-IMPORT: frozen checked provenance bytes changed' }
  $evidence = $utf8.GetString($bytes) | ConvertFrom-Json
  if ($evidence.SourceCommit -cne 'ac5af8e416f906391dc117f083a883acc053a268' -or $evidence.ExitCode -ne 0) {
    throw 'OPT1-CERT-IMPORT: wrong checked source frontier'
  }
  try {
    . (Join-Path $repoRoot $replayProfilePath)
    $profile = Assert-OPT1ReplayProfile -RepoRoot $repoRoot -LeanPath $LeanPath `
      -ExpectedReceiptSHA256 $buildReceiptSHA256
  } catch {
    throw "OPT1-CERT-IMPORT: $($_.Exception.Message)"
  }
  $expected = [ordered]@{}
  foreach ($entry in @($profile.RuntimeImports | Sort-Object Module)) {
    # Keep the live RAW hash map for restoration, separately from the exact
    # canonical source comparison made by the pinned production profile.
    $expected[$entry.Source] = Get-CHash ([IO.File]::ReadAllBytes((Join-Path $repoRoot $entry.Source)))
    $expected[$entry.Artifact] = $entry.ArtifactSHA256
  }
  Assert-CExact @($Hashes.Keys) @($expected.Keys) 'checked import provenance inventory'
  foreach ($path in $expected.Keys) {
    if ($Hashes[$path] -cne $expected[$path]) { throw "OPT1-CERT-IMPORT: source/artifact differs from checked provenance: $path" }
  }
  $script:replayIdentity = [ordered]@{
    SourceCommit=$profile.SourceCommit; SourceProfileSHA256=$profile.SourceProfileSHA256;
    BuildReceiptSHA256=$profile.BuildReceiptSHA256; HistoricalReceiptSHA256=$provenanceSHA256;
    RunnerSHA256=(Get-CHash ([IO.File]::ReadAllBytes((Join-Path $repoRoot $scriptPath))));
    SourceSerialization='strict UTF-8, only CRLF-to-LF; every other byte significant';
    Execution='Lean compiler producer/expected-type consumer checks; not a native machine performance measurement'
  }
}
function Get-CBoundedPath([string]$Path, [string]$Root) {
  $full = [IO.Path]::GetFullPath($Path)
  $prefix = [IO.Path]::GetFullPath($Root).TrimEnd([IO.Path]::DirectorySeparatorChar) + [IO.Path]::DirectorySeparatorChar
  if (-not $full.StartsWith($prefix, [StringComparison]::OrdinalIgnoreCase)) { throw 'OPT1-CERT-LIBRARY: path escapes owned root' }
  return $full
}
function Initialize-CDependencySnapshot {
  $snapshotRoot = Get-CBoundedPath (Join-Path $artifactRoot 'dependency-snapshot') $artifactRoot
  $cacheRoot = Join-Path $repoRoot '.lake/build/lib/lean'
  $entries = [Collections.Generic.List[object]]::new()
  foreach ($path in $importBaseline.Keys) {
    if (-not $path.EndsWith('.olean', [StringComparison]::Ordinal)) { continue }
    $prefix = '.lake/build/lib/lean/'
    if (-not $path.StartsWith($prefix, [StringComparison]::Ordinal)) { throw 'OPT1-CERT-LIBRARY: unexpected cache path' }
    $relative = $path.Substring($prefix.Length)
    if ($privateArtifacts -ccontains $relative) { continue }
    $source = Get-CBoundedPath (Join-Path $repoRoot $path) $cacheRoot
    $destination = Get-CBoundedPath (Join-Path $snapshotRoot $relative) $snapshotRoot
    if ((Get-CHash ([IO.File]::ReadAllBytes($source))) -cne $importBaseline[$path]) { throw 'OPT1-CERT-LIBRARY: cache differs from checked snapshot' }
    [void][IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($destination))
    [IO.File]::Copy($source, $destination, $false)
    if ((Get-CHash ([IO.File]::ReadAllBytes($destination))) -cne $importBaseline[$path]) { throw 'OPT1-CERT-LIBRARY: copied dependency differs' }
    [IO.File]::SetAttributes($destination, ([IO.File]::GetAttributes($destination) -bor [IO.FileAttributes]::ReadOnly))
    $entries.Add([pscustomobject]@{ Artifact=$path; Relative=$relative; Snapshot=$destination; SHA256=$importBaseline[$path]; Bytes=(Get-Item -LiteralPath $destination).Length })
  }
  if ($entries.Count -eq 0) { throw 'OPT1-CERT-LIBRARY: empty immutable dependency closure' }
  Write-CJson (Join-Path $artifactRoot 'dependency-snapshot.json') @($entries)
  return @($entries)
}
function Assert-CPrivateOutput([string]$Library, [string]$Relative, [switch]$MustBeAbsent) {
  if ($privateArtifacts -cnotcontains $Relative) { throw 'OPT1-CERT-LIBRARY: output is not a designated private module' }
  $output = Get-CBoundedPath (Join-Path $Library $Relative) $Library
  if ($MustBeAbsent) {
    if (Test-Path -LiteralPath $output) { throw 'OPT1-CERT-LIBRARY: private output already exists before compile' }
  } else {
    $item = Get-Item -LiteralPath $output
    if ($item.LinkType -or ($item.Attributes -band ([IO.FileAttributes]::ReadOnly -bor [IO.FileAttributes]::ReparsePoint))) {
      throw 'OPT1-CERT-LIBRARY: producer output aliases a dependency or is not private'
    }
  }
  return $output
}
function Initialize-CCaseLibrary([string]$Library) {
  $libraryRoot = Get-CBoundedPath $Library $artifactRoot
  $linked = [Collections.Generic.List[string]]::new()
  foreach ($entry in $dependencySnapshot) {
    if ($privateArtifacts -ccontains $entry.Relative) { throw 'OPT1-CERT-LIBRARY: mutable output in immutable closure' }
    $source = Get-CBoundedPath $entry.Snapshot (Join-Path $artifactRoot 'dependency-snapshot')
    $destination = Get-CBoundedPath (Join-Path $libraryRoot $entry.Relative) $libraryRoot
    if ((Get-CHash ([IO.File]::ReadAllBytes($source))) -cne $entry.SHA256) { throw 'OPT1-CERT-LIBRARY: private dependency snapshot changed' }
    [void][IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($destination))
    New-Item -ItemType HardLink -Path $destination -Value $source -ErrorAction Stop | Out-Null
    $item = Get-Item -LiteralPath $destination
    if ($item.LinkType -cne 'HardLink' -or -not ($item.Attributes -band [IO.FileAttributes]::ReadOnly) -or
        (Get-CHash ([IO.File]::ReadAllBytes($destination))) -cne $entry.SHA256) { throw 'OPT1-CERT-LIBRARY: dependency hardlink verification failed' }
    $linked.Add($entry.Relative)
  }
  Assert-CExact @($linked) @($dependencySnapshot.Relative) 'case dependency closure'
  foreach ($relative in $privateArtifacts) { [void](Assert-CPrivateOutput $libraryRoot $relative -MustBeAbsent) }
  return [ordered]@{ Kind='hardlinks-to-private-readonly-snapshot'; LinkedCount=$linked.Count; SnapshotManifestSHA256=(Get-CHash ([IO.File]::ReadAllBytes((Join-Path $artifactRoot 'dependency-snapshot.json')))); PrivateOutputs=@($privateArtifacts); CacheAliased=$false }
}
function Invoke-CCase([object]$Case) {
  $caseRoot = Join-Path $artifactRoot $Case.Id
  $sourceRoot = Join-Path $caseRoot 'source'
  $library = Join-Path $caseRoot 'lib'
  $originals = @{}
  $record = [ordered]@{ Id=$Case.Id; Kind=$Case.Kind; Field=$Case.Field; Expected=$Case.Verdict;
    ReplayIdentity=$replayIdentity;
    Mode=$(if ($PrepareOnly) { 'PREPARE_ONLY' } else { 'LEAN_REPLAY' }); OriginalHashes=[ordered]@{};
    MutatedHashes=[ordered]@{}; RestoredHashes=[ordered]@{}; ProducersCompiled=$false; ConsumerVerdict='NOT_RUN' }
  try {
    foreach ($path in $sourcePaths) {
      $bytes = [IO.File]::ReadAllBytes((Join-Path $repoRoot $path))
      if ((Get-CHash $bytes) -cne $baseline[$path]) { throw 'OPT1-CERT-SOURCE: original changed after campaign snapshot' }
      $originals[$path] = $bytes
      $destination = Join-Path $sourceRoot $path
      [void][IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($destination))
      [IO.File]::WriteAllBytes($destination, $bytes)
      $record.OriginalHashes[$path] = Get-CHash $bytes
    }
    foreach ($entry in @(@{ Path=$certificatePath; Kind='FIELDS' }, @{ Path=$capstonePath; Kind='INITIALIZERS' })) {
      $text = $utf8.GetString($originals[$entry.Path])
      $changed = Get-CMutatedText $text $entry.Kind $Case
      [IO.File]::WriteAllText((Join-Path $sourceRoot $entry.Path), $changed, $utf8)
    }
    foreach ($path in $sourcePaths) { $record.MutatedHashes[$path] = Get-CHash ([IO.File]::ReadAllBytes((Join-Path $sourceRoot $path))) }
    if ($record.MutatedHashes[$consumerPath] -cne $record.OriginalHashes[$consumerPath]) { throw 'OPT1-CERT-MUTATION: fixed consumer bytes changed' }
    if ($Case.Verdict -ceq 'REJECT' -and
        ($record.MutatedHashes[$certificatePath] -ceq $record.OriginalHashes[$certificatePath] -or
         $record.MutatedHashes[$capstonePath] -ceq $record.OriginalHashes[$capstonePath])) { throw 'OPT1-CERT-MUTATION: selected producer mutation was empty' }
    if (-not $PrepareOnly) {
      $record.DependencyLibrary = Initialize-CCaseLibrary $library
      $record.PrivateOutputHashes = [ordered]@{}
      $environment = @{ LEAN_PATH=$library;
        LEAN_SYSROOT=([IO.Path]::GetFullPath((Join-Path ([IO.Path]::GetDirectoryName($LeanPath)) '..'))) }
      foreach ($path in @($certificatePath, $capstonePath)) {
        $relativeOutput = $path.Substring(0, $path.Length - 5) + '.olean'
        $output = Assert-CPrivateOutput $library $relativeOutput -MustBeAbsent
        [void][IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($output))
        $name = $Case.Id + '-' + [IO.Path]::GetFileNameWithoutExtension($path)
        $result = Invoke-CProcess $name $LeanPath @('-j1', '-o', $output, $path) $sourceRoot $environment
        Assert-CAccepted $result
        [void](Assert-CPrivateOutput $library $relativeOutput)
        $record.PrivateOutputHashes[$relativeOutput] = Get-CHash ([IO.File]::ReadAllBytes($output))
      }
      $record.ProducersCompiled = $true
      [void](Assert-CPrivateOutput $library $privateArtifacts[2] -MustBeAbsent)
      $result = Invoke-CProcess ($Case.Id + '-Consumers') $LeanPath @('-j1', $consumerPath) $sourceRoot $environment
      if ($Case.Verdict -ceq 'ACCEPT') { Assert-CAccepted $result }
      else { Assert-CRejected $result ($utf8.GetString($originals[$consumerPath])) $Case }
      [void](Assert-CPrivateOutput $library $privateArtifacts[2] -MustBeAbsent)
      $record.ConsumerVerdict = $Case.Verdict
    }
  } finally {
    $restoreErrors = [Collections.Generic.List[string]]::new()
    foreach ($path in $originals.Keys) {
      try {
        [IO.File]::WriteAllBytes((Join-Path $sourceRoot $path), $originals[$path])
        $restored = Get-CHash ([IO.File]::ReadAllBytes((Join-Path $sourceRoot $path)))
        $record.RestoredHashes[$path] = $restored
        if ($restored -cne $record.OriginalHashes[$path]) { throw "isolated copy differs at $path" }
      } catch { $restoreErrors.Add($_.Exception.Message) }
    }
    if (Test-Path -LiteralPath $caseRoot) { Write-CJson (Join-Path $caseRoot 'case.json') $record }
    if ($restoreErrors.Count -ne 0) { throw "OPT1-CERT-RESTORATION: $($restoreErrors -join ' | ')" }
  }
  $receipt = if ($PrepareOnly) { 'PREPARED' } else { $Case.Verdict }
  Write-Host "OPT1-CERT CASE $($Case.Id) $receipt restored=True"
}
function Expect-CRejection([scriptblock]$Action, [string]$Prefix) {
  $rejected = $false
  try { & $Action | Out-Null } catch { if (-not $_.Exception.Message.StartsWith($Prefix)) { throw }; $rejected = $true }
  if (-not $rejected) { throw 'OPT1-CERT-SELFTEST: expected rejection was accepted' }
}
function Invoke-CRegistryTests {
  Assert-CRegistry
  Expect-CRejection { Assert-CRegistry -IDs @() } 'OPT1-CERT-REGISTRY:'
  Expect-CRejection { Assert-CRegistry -IDs @($registry.Id)[1..79] } 'OPT1-CERT-REGISTRY:'
  Expect-CRejection { Assert-CRegistry -IDs (@($registry.Id) + @($registry[0].Id)) } 'OPT1-CERT-REGISTRY:'
  $swapped = @($registry.Id); $swapped[0] = $registry[1].Id; $swapped[1] = $registry[0].Id
  Expect-CRejection { Assert-CRegistry -IDs $swapped } 'OPT1-CERT-REGISTRY:'
  $certificate = Read-CSource $certificatePath
  $consumer = Read-CSource $consumerPath
  foreach ($case in @($registry | Where-Object { $_.Verdict -ceq 'REJECT' })) {
    Expect-CRejection { Assert-CRegistry -Certificate (Get-CMutatedText $certificate 'FIELDS' $case) } 'OPT1-CERT-REGISTRY:'
  }
  Expect-CRejection { Assert-CRegistry -Consumer $consumer.Replace('certificate.widthBounds', 'certificate.memoryWordsFit') } 'OPT1-CERT-REGISTRY:'
  $line = ($consumer.Substring(0, $consumer.IndexOf('  certificate.widthBounds')) -split "`n").Count
  $weaken = @($registry | Where-Object { $_.Id -ceq 'W03-widthBounds' })[0]
  $deletion = @($registry | Where-Object { $_.Id -ceq 'D03-widthBounds' })[0]
  $fake = [pscustomobject]@{ Stage='diagnostic-fixture'; ExitCode=1; TimedOut=$false; OutputLimitExceeded=$false;
    StandardError=@(); Output=@("${consumerPath}:${line}:2: error: type mismatch", '  certificate.widthBounds') }
  Assert-CRejected $fake $consumer $weaken
  $fake.StandardError = @('error: cannot open file')
  $fake.Output += 'error: cannot open file'
  Expect-CRejection { Assert-CRejected $fake $consumer $weaken } 'OPT1-CERT-VERDICT:'
  $fake.StandardError = @('uncaught exception: failed to write output')
  $fake.Output = @("${consumerPath}:${line}:2: error: type mismatch", '  certificate.widthBounds') + $fake.StandardError
  Expect-CRejection { Assert-CRejected $fake $consumer $weaken } 'OPT1-CERT-VERDICT:'
  $fake.StandardError = @()
  $fake.Output = @("${consumerPath}:${line}:2: error: type mismatch", '  certificate.widthBounds', '  "error: quoted diagnostic text"')
  Assert-CRejected $fake $consumer $weaken
  Expect-CRejection { Assert-CRejected $fake $consumer $deletion } 'OPT1-CERT-VERDICT:'
  Expect-CRejection { Assert-CRejected $fake $consumer $registry[2] } 'OPT1-CERT-VERDICT:'
  $fake.Output = @("${consumerPath}:${line}:2: error: Invalid field widthBounds")
  Assert-CRejected $fake $consumer $deletion
  $fake.Output += 'maximum heartbeats exceeded'
  Expect-CRejection { Assert-CRejected $fake $consumer $deletion } 'OPT1-CERT-VERDICT:'
  $fake.ExitCode = 0
  $fake.Output = @()
  Assert-CAccepted $fake
  Expect-CRejection { Assert-CRejected $fake $consumer $deletion } 'OPT1-CERT-VERDICT:'
  Write-Host 'OPT1-CERT-REGISTRY SELF-TEST PASS exact=80 missing/duplicate/reordered/all78mutations/fixed-consumer/exact-diagnostic/mixed-unlocated-error/mixed-uncaught-exception/indented-detail/resource/accept'
}
function Invoke-CLibraryTests {
  $library = Join-Path $artifactRoot 'library-control/lib'
  $record = Initialize-CCaseLibrary $library
  $record.PrivateControls = [ordered]@{}
  foreach ($relative in $privateArtifacts) {
    $output = Assert-CPrivateOutput $library $relative -MustBeAbsent
    [void][IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($output))
    [IO.File]::WriteAllText($output, 'OPT1 private output control; not a Lean artifact', $utf8)
    [void](Assert-CPrivateOutput $library $relative)
    Expect-CRejection { [void](Assert-CPrivateOutput $library $relative -MustBeAbsent) } 'OPT1-CERT-LIBRARY:'
    $record.PrivateControls[$relative] = 'private-write-pass/existing-output-rejected'
  }
  $aliasLibrary = Join-Path $artifactRoot 'alias-control/lib'
  $alias = Join-Path $aliasLibrary $privateArtifacts[0]
  [void][IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($alias))
  New-Item -ItemType HardLink -Path $alias -Value $dependencySnapshot[0].Snapshot -ErrorAction Stop | Out-Null
  Expect-CRejection { [void](Assert-CPrivateOutput $aliasLibrary $privateArtifacts[0]) } 'OPT1-CERT-LIBRARY:'
  Expect-CRejection { [void](Get-CBoundedPath (Join-Path $artifactRoot '../escape') $artifactRoot) } 'OPT1-CERT-LIBRARY:'
  $firstPath = @($importBaseline.Keys)[0]
  $oldHash = $importBaseline[$firstPath]
  try {
    $importBaseline[$firstPath] = '0' * 64
    Expect-CRejection { Assert-CImportProvenance $importBaseline } 'OPT1-CERT-IMPORT:'
  } finally { $importBaseline[$firstPath] = $oldHash }
  $record.AliasRejected = $true
  $record.EscapeRejected = $true
  $record.ChangedProvenanceRejected = $true
  $record.LeanLaunched = $false
  Write-CJson (Join-Path $artifactRoot 'library-control.json') $record
  Write-Host "OPT1-CERT-LIBRARY SELF-TEST PASS dependencies=$($record.LinkedCount) private=3 alias/escape/provenance=reject no-Lean"
}
function Invoke-CSelectorTests {
  $wrapper = Join-Path $artifactRoot 'selector-boundary.ps1'
  [IO.File]::WriteAllText($wrapper, @'
param([string]$Target, [string]$Mode)
$ErrorActionPreference = 'Stop'
switch ($Mode) {
  'omitted' { & $Target -SelectorProbeOnly }
  'valid' { & $Target -SelectorProbeOnly -OnlyCase 'A01-UNCHANGED' }
  'valid-reject' { & $Target -SelectorProbeOnly -OnlyCase 'W03-widthBounds' }
  'empty' { & $Target -OnlyCase '' }
  'whitespace' { & $Target -OnlyCase ' ' }
  'malformed' { & $Target -OnlyCase 'A01-UNCHANGED,W01-x' }
  'zero' { & $Target -OnlyCase '0' }
  'unknown' { & $Target -OnlyCase 'D99-unknown' }
  'duplicate' { try { & $Target -OnlyCase 'A01-UNCHANGED' -OnlyCase 'A02-COMMENT' } catch { Write-Host 'OPT1-CERT-BOUNDARY: duplicate parameter rejected'; $global:LASTEXITCODE=1 } }
}
exit ([int]$LASTEXITCODE)
'@, $utf8)
  $shellPath = (Get-Process -Id $PID).Path
  foreach ($mode in @('omitted', 'valid', 'valid-reject', 'empty', 'whitespace', 'malformed', 'zero', 'unknown', 'duplicate')) {
    $result = Invoke-CProcess "selector-$mode" $shellPath @('-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', $wrapper, '-Target', (Join-Path $repoRoot $scriptPath), '-Mode', $mode) $repoRoot
    $expectedExit = if ($mode -in @('omitted', 'valid', 'valid-reject')) { 0 } else { 1 }
    $token = switch ($mode) {
      'omitted' { 'OPT1-CERT-SELECTOR PROBE PASS bound=False selected=80' }
      'valid' { 'OPT1-CERT-SELECTOR PROBE PASS bound=True selected=1 ids=A01-UNCHANGED' }
      'valid-reject' { 'OPT1-CERT-SELECTOR PROBE PASS bound=True selected=1 ids=W03-widthBounds' }
      'empty' { 'OPT1-CERT-SELECTOR: explicitly empty selector' }
      'whitespace' { 'OPT1-CERT-SELECTOR: explicitly empty selector' }
      'malformed' { 'OPT1-CERT-SELECTOR: malformed selector' }
      'zero' { 'OPT1-CERT-SELECTOR: malformed selector' }
      'unknown' { 'OPT1-CERT-SELECTOR: unknown selector D99-unknown' }
      'duplicate' { 'OPT1-CERT-BOUNDARY: duplicate parameter rejected' }
    }
    $joined = $result.Output -join "`n"
    if ($result.ExitCode -ne $expectedExit -or -not $joined.Contains($token) -or $joined -match 'OPT1-CERT-STAGE|OPT1-CERT CASE') {
      throw "OPT1-CERT-BOUNDARY: $mode incorrect verdict or reached semantic execution"
    }
  }
  Write-Host 'OPT1-CERT-BOUNDARY SELF-TEST PASS executed=9 expected=9'
}

try {
  $selected = @(Get-CSelection)
  Assert-CRegistry
  if (@(@($PrepareOnly, $RegistrySelfTestOnly, $LibrarySelfTestOnly, $SelectorProbeOnly, $SelectorBoundarySelfTestOnly) | Where-Object { $_ }).Count -gt 1 -or
      ($onlyCaseBound -and ($RegistrySelfTestOnly -or $LibrarySelfTestOnly -or $SelectorBoundarySelfTestOnly))) { throw 'OPT1-CERT-SELECTOR: incompatible modes' }
  if ($SelectorProbeOnly) { Write-Host "OPT1-CERT-SELECTOR PROBE PASS bound=$onlyCaseBound selected=$($selected.Count) ids=$($selected.Id -join ',')" }
  elseif ($RegistrySelfTestOnly) { Invoke-CRegistryTests }
  else {
    . (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
    # Short private names keep the complete case dependency hierarchy within
    # ordinary Windows hardlink path limits, including long field selectors.
    $artifactRoot = Join-Path $repoRoot ('.lake/oc/' + [Guid]::NewGuid().ToString('N').Substring(0, 12))
    [void][IO.Directory]::CreateDirectory($artifactRoot)
    Write-Host "OPT1-CERT-ARTIFACTS $artifactRoot"
    if ($SelectorBoundarySelfTestOnly) { Invoke-CSelectorTests }
    else {
      $baseline = Get-COriginalSnapshot
      Write-CJson (Join-Path $artifactRoot 'original-before.json') $baseline
      $initialStatus = Get-CTrackedStatus 'before'
      Write-CJson (Join-Path $artifactRoot 'tracked-status-before.json') @{ Status=$initialStatus; Clean=($initialStatus -ceq '') }
      if (-not $PrepareOnly -and -not $LibrarySelfTestOnly -and -not (Test-Path -LiteralPath $LeanPath -PathType Leaf)) { throw 'OPT1-CERT-PROCESS: exact Lean unavailable' }
      if (-not $PrepareOnly) {
        $importBaseline = Get-CImportSnapshot
        Write-CJson (Join-Path $artifactRoot 'imports-before.json') $importBaseline
        $dependencySnapshot = @(Initialize-CDependencySnapshot)
      }
      if ($LibrarySelfTestOnly) { Invoke-CLibraryTests }
      else {
        $executed = [Collections.Generic.List[string]]::new()
        foreach ($case in $selected) { Invoke-CCase $case; $executed.Add($case.Id) }
        Assert-CExact @($executed) @($selected.Id) 'executed/expected cases'
        Write-CJson (Join-Path $artifactRoot 'executed.json') @{ Version=$version; Expected=@($selected.Id); Executed=@($executed); PrepareOnly=[bool]$PrepareOnly; ReplayIdentity=$replayIdentity }
        $mode = if ($PrepareOnly) { 'PREPARE' } else { 'REPLAY' }
        $completion = "OPT1-CERT-$mode PASS executed=$($executed.Count) expected=$($selected.Count) registry=$version"
      }
    }
  }
} catch { $exitCode=1; [Console]::Error.WriteLine($_.Exception.Message) }
finally {
  if ($null -ne $baseline) {
    try {
      $after = Get-COriginalSnapshot
      Write-CJson (Join-Path $artifactRoot 'original-after.json') $after
      if (($baseline | ConvertTo-Json -Compress) -cne ($after | ConvertTo-Json -Compress)) { throw 'OPT1-CERT-RESTORATION: tracked original source hashes changed' }
      $finalStatus = Get-CTrackedStatus 'after'
      Write-CJson (Join-Path $artifactRoot 'tracked-status-after.json') @{ Status=$finalStatus; Clean=($finalStatus -ceq '') }
      if ($finalStatus -cne $initialStatus) { throw 'OPT1-CERT-RESTORATION: initial tracked-source status changed' }
      if ($null -ne $importBaseline) {
        $importAfter = [ordered]@{}
        foreach ($path in $importBaseline.Keys) { $importAfter[$path] = Get-CHash ([IO.File]::ReadAllBytes((Join-Path $repoRoot $path))) }
        Write-CJson (Join-Path $artifactRoot 'imports-after.json') $importAfter
        if (($importAfter | ConvertTo-Json -Compress) -cne ($importBaseline | ConvertTo-Json -Compress)) { throw 'OPT1-CERT-RESTORATION: task-local import source/artifact hashes changed' }
        # Recheck the complete canonical source/configuration/toolchain/artifact
        # profile too, including validator/Consumers outputs outside the runtime
        # import map. Raw restoration above stays a separate check.
        . (Join-Path $repoRoot $replayProfilePath)
        $null = Assert-OPT1ReplayProfile -RepoRoot $repoRoot -LeanPath $LeanPath `
          -ExpectedReceiptSHA256 $buildReceiptSHA256
      }
      if ($null -ne $dependencySnapshot) {
        foreach ($entry in $dependencySnapshot) {
          if ((Get-CHash ([IO.File]::ReadAllBytes($entry.Snapshot))) -cne $entry.SHA256) { throw 'OPT1-CERT-RESTORATION: private immutable dependency snapshot changed' }
        }
      }
      Write-Host 'OPT1-CERT-ORIGINALS PASS source SHA256 unchanged; mutations applied/restored only in isolated copies'
    } catch { $exitCode=1; [Console]::Error.WriteLine($_.Exception.Message) }
  }
  if ($null -ne $artifactRoot) { Write-CJson (Join-Path $artifactRoot 'summary.json') @{ ExitCode=$exitCode; Version=$version; Stages=@($stages); TrackedSourceMutations=0; PrepareOnly=[bool]$PrepareOnly; LibrarySelfTestOnly=[bool]$LibrarySelfTestOnly; ReplayIdentity=$replayIdentity } }
}
if ($exitCode -eq 0 -and $null -ne $completion) { Write-Host $completion }
exit $exitCode
