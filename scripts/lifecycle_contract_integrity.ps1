#!/usr/bin/env pwsh
[CmdletBinding()]
param(
  [string]$RepositoryRoot,
  [string]$MatrixPath,
  [string]$SourcePrompt
)

# A read-only, whole-contract check: no selectors, subprocesses or source edits.
# The exact prompt is embedded in CONTRACT_REQUIREMENTS.json so a fresh checkout
# does not require the coordinator's external directory. -SourcePrompt also
# verifies the original external bytes when they are available.
$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
$utf8 = New-Object System.Text.UTF8Encoding($false, $true)
$sourceHash = 'f82a24460dfa06602fc52e2c78b0fa8402fbb84a0d203b4abb95040fa56b0c18'
$contractHash = '5bd95d24b6cffaf9fb39abb2aa04cca9743aed7884b3f87d03d7428e6b9cd8eb'
$baselineHash = '8b08e2d7c7f284634d88bfa4262ee447f79a401c78b27dc346ea34d76ccba4a7'
$marker = '<!-- APPEND-ONLY-EVIDENCE -->'
$header = '| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |'
$expectedIds = @((1..20 | ForEach-Object { 'L1-{0:D2}' -f $_ })) + @(
  'INV-STORE-IDENTITY', 'INV-VALUE-DEPENDENCY', 'INV-SEMANTIC-NONVACUITY',
  'INV-TRACE-EXECUTION', 'INV-STORE-AGREEMENT', 'INV-READ-BACKING',
  'INV-WORD-WIDTH', 'INV-ADDRESS-WIDTH', 'INV-INSTRUCTION-ATOMICITY',
  'INV-PROGRAM-ACCOUNTING', 'INV-ORACLE-INDEPENDENCE', 'INV-VALIDATION-REACH',
  'INV-ALL-SIZE', 'INV-PROOF-SEPARATION', 'INV-NO-SYNTHETIC',
  'INV-CATEGORY-SEPARATION', 'INV-PUBLIC-COMPOSITION',
  'INV-CERTIFICATE-ANTI-BYPASS', 'INV-MUTATION-REPRODUCIBILITY',
  'INV-GLOBAL-PHYSICAL-MACHINE', 'INV-WIDTH-SCALING', 'CHK-FINAL', 'CHK-SCOPE'
)

function Fail([string]$Code, [string]$Detail) {
  throw "${Code}: $Detail"
}

function Sha256([byte[]]$Bytes) {
  $hasher = [System.Security.Cryptography.SHA256]::Create()
  try { return ([BitConverter]::ToString($hasher.ComputeHash($Bytes))).Replace('-', '').ToLowerInvariant() }
  finally { $hasher.Dispose() }
}

function ReadStrict([string]$Path) {
  $bytes = [IO.File]::ReadAllBytes($Path)
  try { $value = $utf8.GetString($bytes) }
  catch { Fail 'UTF8' "invalid strict UTF-8 in $Path" }
  if ($value.StartsWith([string][char]0xFEFF, [StringComparison]::Ordinal)) { Fail 'UTF8' "unexpected BOM in $Path" }
  # This supplemental mojibake check never replaces complete byte comparisons.
  foreach ($bad in @(([string][char]0x00C2 + [char]0x00AC),
      ([string][char]0x00E2 + [char]0x20AC), ([string][char]0xFFFD))) {
    if ($value.Contains($bad)) { Fail 'UTF8' "recognizable mojibake in $Path" }
  }
  return [PSCustomObject]@{ Bytes = $bytes; Text = $value }
}

function RequireIds([object[]]$Ids, [string]$Origin) {
  $seen = @{}
  foreach ($id in $Ids) {
    if ($expectedIds -cnotcontains $id) { Fail 'ID_UNKNOWN' "$Origin contains $id" }
    if ($seen.ContainsKey($id)) { Fail 'ID_DUPLICATE' "$Origin repeats $id" }
    $seen[$id] = $true
  }
  if ($Ids.Count -ne $expectedIds.Count) { Fail 'ID_MISSING' "$Origin has $($Ids.Count) of 43 rows" }
  for ($i = 0; $i -lt $expectedIds.Count; $i++) {
    if ($Ids[$i] -cne $expectedIds[$i]) { Fail 'ID_ORDER' "$Origin differs at index $i" }
  }
}

function ParseRows([string]$Text, [string]$Origin) {
  if ([regex]::Matches($Text, [regex]::Escape($marker)).Count -ne 1) {
    Fail 'MARKER' "$Origin requires exactly one append-only marker"
  }
  $prefix = $Text.Substring(0, $Text.IndexOf($marker, [StringComparison]::Ordinal))
  $lines = @($prefix -split "`n")
  if (@($lines | Where-Object { $_ -ceq $header }).Count -ne 1) {
    Fail 'HEADER' "$Origin requires the exact eight-column header"
  }
  $rows = @()
  foreach ($line in $lines) {
    if (-not $line.StartsWith('|')) { continue }
    if ($line -ceq $header -or $line -ceq '| --- | --- | --- | --- | --- | --- | --- | --- |') { continue }
    $parts = @($line -split '\|')
    if ($parts.Count -ne 10 -or $parts[0] -cne '' -or $parts[9] -cne '') {
      Fail 'COLUMNS' "$Origin has a row without exactly eight columns"
    }
    $cells = @($parts[1..8] | ForEach-Object { $_.Trim() })
    if (@($cells | Where-Object { [string]::IsNullOrWhiteSpace($_) }).Count) {
      Fail 'COLUMNS' "$Origin has an empty column"
    }
    if ($cells[0] -cnotmatch '^`(L1-[0-9]{2}|INV-[A-Z-]+|CHK-[A-Z-]+)`$') {
      Fail 'ID_FORMAT' "$Origin has an invalid ID cell"
    }
    $rows += [PSCustomObject]@{ Id = $Matches[1]; Requirement = $cells[1]; Line = $line }
  }
  RequireIds @($rows | ForEach-Object { $_.Id }) $Origin
  # Evidence uses headings/prose, never a second acceptance-row table that could
  # conceal duplicate or replacement dispositions among immutable rows.
  $suffix = $Text.Substring($prefix.Length + $marker.Length)
  if ($suffix -cmatch '(?m)^\|\s*`?(?:L1-|INV-|CHK-)') {
    Fail 'EVIDENCE_ROW' "$Origin appends a duplicate acceptance-row table"
  }
  return $rows
}

try {
  foreach ($name in @('RepositoryRoot', 'MatrixPath', 'SourcePrompt')) {
    if ($PSBoundParameters.ContainsKey($name) -and
        [string]::IsNullOrWhiteSpace([string]$PSBoundParameters[$name])) {
      Fail 'ARGUMENT' "$name was explicitly empty"
    }
  }
  if (-not $PSBoundParameters.ContainsKey('RepositoryRoot')) {
    $RepositoryRoot = Split-Path $PSScriptRoot -Parent
  }
  $root = [IO.Path]::GetFullPath($RepositoryRoot)
  $directory = Join-Path $root 'docs/internal/extensions/lifecycle1'
  if (-not $PSBoundParameters.ContainsKey('MatrixPath')) {
    $MatrixPath = Join-Path $directory 'ACCEPTANCE_MATRIX.md'
  } elseif (-not [IO.Path]::IsPathRooted($MatrixPath)) {
    $MatrixPath = Join-Path $root $MatrixPath
  }
  $contractFile = ReadStrict (Join-Path $directory 'CONTRACT_REQUIREMENTS.json')
  if ((Sha256 $contractFile.Bytes) -cne $contractHash) { Fail 'CONTRACT_HASH' 'frozen source/requirements JSON changed' }
  $contract = $contractFile.Text | ConvertFrom-Json
  RequireIds @($contract.expected_ids) 'contract expected IDs'
  RequireIds @($contract.requirements | ForEach-Object { $_.id }) 'contract requirements'
  $promptBytes = $utf8.GetBytes([string]$contract.source_prompt.text)
  if ((Sha256 $promptBytes) -cne $sourceHash -or
      $promptBytes.Length -ne 33909 -or
      $contract.source_prompt.sha256 -cne $sourceHash) { Fail 'PROMPT_HASH' 'embedded exact source prompt changed' }
  if ($PSBoundParameters.ContainsKey('SourcePrompt')) {
    $external = ReadStrict $SourcePrompt
    if ((Sha256 $external.Bytes) -cne $sourceHash) { Fail 'PROMPT_HASH' 'external source prompt bytes differ' }
  }
  $sourceRows = @([regex]::Matches($contract.source_prompt.text,
    '(?m)^- (L1-[0-9]{2}|INV-[A-Z-]+|CHK-[A-Z-]+): ([^\r\n]*(?:\r?\n[ \t]+[^\r\n]+)*)'))
  RequireIds @($sourceRows | ForEach-Object { $_.Groups[1].Value }) 'source prompt'
  $baseline = ReadStrict (Join-Path $directory 'ACCEPTANCE_MATRIX.frozen.md')
  $candidate = ReadStrict $MatrixPath
  $frozenRows = @(ParseRows $baseline.Text 'frozen baseline')
  $activeRows = @(ParseRows $candidate.Text 'candidate matrix')
  for ($i = 0; $i -lt 43; $i++) {
    # Joining source wraps is permitted only for the initial requirement
    # extraction. No candidate/frozen row normalization is used in comparisons.
    $requirement = (@($sourceRows[$i].Groups[2].Value -split '\r?\n' |
      ForEach-Object { $_.Trim() }) -join ' ')
    foreach ($actual in @($contract.requirements[$i].requirement,
        $frozenRows[$i].Requirement, $activeRows[$i].Requirement)) {
      if (-not [string]::Equals([string]$actual, $requirement, [StringComparison]::Ordinal)) {
        Fail 'REQUIREMENT' "complete requirement differs from source: $($expectedIds[$i])"
      }
    }
    if (-not [string]::Equals($activeRows[$i].Line, $frozenRows[$i].Line, [StringComparison]::Ordinal)) {
      Fail 'ROW_BYTES' "complete frozen row changed: $($expectedIds[$i])"
    }
  }
  if ((Sha256 $baseline.Bytes) -cne $baselineHash) { Fail 'BASELINE_HASH' 'complete initial baseline bytes changed' }
  if (-not $candidate.Text.StartsWith($baseline.Text, [StringComparison]::Ordinal)) {
    Fail 'PREFIX_BYTES' 'candidate changed the frozen prefix instead of appending evidence'
  }
  Write-Output 'LIFECYCLE-CONTRACT: PASS rows=43 columns=8 changed_ids=[]'
  Write-Output "LIFECYCLE-CONTRACT: source_sha256=$sourceHash baseline_sha256=$baselineHash"
  Write-Output "LIFECYCLE-CONTRACT: matrix_sha256=$(Sha256 $candidate.Bytes) matrix_bytes=$($candidate.Bytes.Length)"
  Write-Output 'LIFECYCLE-CONTRACT: this checks contract integrity, not acceptance-row closure'
  exit 0
} catch {
  Write-Output "LIFECYCLE-CONTRACT: FAIL $($_.Exception.Message)"
  exit 1
}
