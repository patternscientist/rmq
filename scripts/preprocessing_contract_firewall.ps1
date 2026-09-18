[CmdletBinding()]
param()
$ErrorActionPreference = 'Stop'
$pre1Root = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$utf8Strict = [Text.UTF8Encoding]::new($false, $true)

# The operational import closure is explicitly finite. Controls and Contract
# are specification/audit consumers and cannot be dependencies of these roots.
$allowedImports = [ordered]@{
  'RMQ/Core/WordRAM/Construction/Primitive.lean' = @('Std')
  'RMQ/Core/WordRAM/Construction/Input.lean' = @('Std')
  'RMQ/Core/WordRAM/Construction/Model.lean' = @(
    'RMQ.Core.WordRAM.Construction.Primitive',
    'RMQ.Core.WordRAM.Construction.Input')
}

function Remove-LeanComments([string]$source) {
  $out = [Text.StringBuilder]::new()
  $depth = 0
  $lineComment = $false
  $quoted = $false
  for ($index = 0; $index -lt $source.Length; $index++) {
    $current = $source[$index]
    $pair = if ($index + 1 -lt $source.Length) { $source.Substring($index, 2) } else { '' }
    if ($lineComment) {
      if ($current -eq "`n") { $lineComment = $false; [void]$out.Append("`n") }
      else { [void]$out.Append(' ') }
    } elseif ($depth -gt 0) {
      if ($pair -ceq '/-') { $depth++; $index++; [void]$out.Append('  ') }
      elseif ($pair -ceq '-/') { $depth--; $index++; [void]$out.Append('  ') }
      elseif ($current -eq "`n") { [void]$out.Append("`n") }
      else { [void]$out.Append(' ') }
    } elseif ($quoted) {
      # Keep string contents inert, including words that look like imports.
      if ($current -eq '\') { $index++; [void]$out.Append('  ') }
      elseif ($current -eq '"') { $quoted = $false; [void]$out.Append(' ') }
      elseif ($current -eq "`n") { [void]$out.Append("`n") }
      else { [void]$out.Append(' ') }
    } elseif ($pair -ceq '--') { $lineComment = $true; $index++; [void]$out.Append('  ') }
    elseif ($pair -ceq '/-') { $depth = 1; $index++; [void]$out.Append('  ') }
    elseif ($current -eq '"') { $quoted = $true; [void]$out.Append(' ') }
    else { [void]$out.Append($current) }
  }
  if ($depth -ne 0 -or $quoted) { throw 'PRE1-FIREWALL unterminated comment/string' }
  return $out.ToString()
}

try {
  foreach ($relative in $allowedImports.Keys) {
    $path = Join-Path $pre1Root $relative
    $source = $utf8Strict.GetString([IO.File]::ReadAllBytes($path))
    $code = Remove-LeanComments $source
    $imports = @([regex]::Matches($code, '(?m)^\s*import\s+([^\r\n]+)') | ForEach-Object {
      $_.Groups[1].Value.Trim() -split '\s+'
    })
    $expected = @($allowedImports[$relative])
    if ($imports.Count -ne $expected.Count -or
        (@(Compare-Object -CaseSensitive $imports $expected)).Count -ne 0 -or
        (@($imports | Select-Object -Unique)).Count -ne $imports.Count) {
      throw "PRE1-FIREWALL imports rejected: $relative actual=[$($imports -join ',')]"
    }
    # Any nonstandard header directive or import syntax is rejected, not
    # silently omitted. Lean's own compiler still validates the source.
    $remaining = [regex]::Replace($code, '(?m)^\s*import\s+[^\r\n]+', '')
    if ($remaining -match '\b(import|prelude)\b') {
      throw "PRE1-FIREWALL unrecognized import/header syntax: $relative"
    }
  }
  $manifestPath = Join-Path $pre1Root 'docs/internal/extensions/pre1/primitive_manifest.json'
  $manifest = $utf8Strict.GetString([IO.File]::ReadAllBytes($manifestPath)) | ConvertFrom-Json
  if ($manifest.version -ne 1 -or @($manifest.files).Count -ne $allowedImports.Count) {
    throw 'PRE1-FIREWALL exact primitive registry version/count'
  }
  $seen = @{}
  foreach ($entry in $manifest.files) {
    if (-not $allowedImports.Contains($entry.path) -or $seen.ContainsKey($entry.path)) {
      throw 'PRE1-FIREWALL duplicate/unknown primitive path'
    }
    $seen[$entry.path] = $true
    $raw = [IO.File]::ReadAllBytes((Join-Path $pre1Root $entry.path))
    $normalized = $utf8Strict.GetString($raw).Replace("`r`n", "`n")
    $sha = [Security.Cryptography.SHA256]::Create()
    try { $actual = [BitConverter]::ToString($sha.ComputeHash($utf8Strict.GetBytes($normalized))).Replace('-', '') }
    finally { $sha.Dispose() }
    if ($actual -cne $entry.sha256) {
      throw "PRE1-FIREWALL frozen primitive bytes changed: $($entry.path)"
    }
  }
  Write-Output 'PRE1-FIREWALL PASS: exact Std-only primitive closure and frozen evaluator bytes'
  exit 0
} catch { Write-Output $_.Exception.Message; exit 1 }
