[CmdletBinding()]
param(
  # Own deadline for the nested contract-guard child (audit PRE-1-A1C P3-7).
  # Evidence (this host, 2026-09-13): the standalone contract guard took 2.2 s
  # and shell startup has been measured at 9.0 s; the replay bounds the whole
  # firewall stage by 120 s, so 60 s stays inside it with more than 5x margin.
  [ValidateRange(1, 3600)][int]$ContractGuardDeadlineSeconds = 60
)
$ErrorActionPreference = 'Stop'
$pre1Root = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$utf8Strict = [Text.UTF8Encoding]::new($false, $true)

# Layer 1 is the frozen contract guard over Primitive/Input/Model. It runs first
# as a child process and its exact PASS line is required. Layer 2 is this table:
# the builder closure, repository-relative path -> exact direct imports. A new
# Builder/*.lean module is registered by appending one entry here and one entry
# to builder_manifest.json; nothing else changes.
$allowedImports = [ordered]@{
  'RMQ/Core/WordRAM/Construction/Program.lean' = @('RMQ.Core.WordRAM.Construction.Model')
  'RMQ/Core/WordRAM/Construction/Calculus.lean' = @('RMQ.Core.WordRAM.Construction.Program')
  'RMQ/Core/WordRAM/Construction/Safety.lean' = @('RMQ.Core.WordRAM.Construction.Program')
  'RMQ/Core/WordRAM/Construction/Structured.lean' = @(
    'RMQ.Core.WordRAM.Construction.Calculus',
    'RMQ.Core.WordRAM.Construction.Safety')
  'RMQ/Core/WordRAM/Construction/Compiler.lean' = @('RMQ.Core.WordRAM.Construction.Structured')
  'RMQ/Core/WordRAM/Construction/Loop.lean' = @('RMQ.Core.WordRAM.Construction.Compiler')
  'RMQ/Core/WordRAM/Construction/ArrayRun.lean' = @('RMQ.Core.WordRAM.Construction.Program')
  'RMQ/Core/WordRAM/Construction/Builder/Registers.lean' = @('RMQ.Core.WordRAM.Construction.Loop')
  'RMQ/Core/WordRAM/Construction/Builder/Emit.lean' = @('RMQ.Core.WordRAM.Construction.Builder.Registers')
  'RMQ/Core/WordRAM/Construction/Builder/Geometry.lean' = @('RMQ.Core.WordRAM.Construction.Builder.Emit')
  'RMQ/Core/WordRAM/Construction/Builder/Interior.lean' = @('RMQ.Core.WordRAM.Construction.Builder.Geometry')
  'RMQ/Core/WordRAM/Construction/Builder/Access.lean' = @('RMQ.Core.WordRAM.Construction.Builder.Interior')
  'RMQ/Core/WordRAM/Construction/Builder/Cartesian.lean' = @('RMQ.Core.WordRAM.Construction.Builder.Interior')
  'RMQ/Core/WordRAM/Construction/Builder/Program.lean' = @('RMQ.Core.WordRAM.Construction.Builder.Output')
  'RMQ/Core/WordRAM/Construction/Builder/Micro.lean' = @('RMQ.Core.WordRAM.Construction.Builder.Access')
  'RMQ/Core/WordRAM/Construction/Builder/Finish.lean' = @(
    'RMQ.Core.WordRAM.Construction.Builder.Micro',
    'RMQ.Core.WordRAM.Construction.Builder.Cartesian')
  'RMQ/Core/WordRAM/Construction/Builder/Output.lean' = @('RMQ.Core.WordRAM.Construction.Builder.Finish')
}
# The closure may import these roots. Their own imports are the contract
# guard's responsibility and are not re-walked here.
$contractRoots = @(
  'RMQ.Core.WordRAM.Construction.Primitive',
  'RMQ.Core.WordRAM.Construction.Input',
  'RMQ.Core.WordRAM.Construction.Model')
$modulePrefix = 'RMQ.Core.WordRAM.Construction.'
$contractGuardPass = 'PRE1-FIREWALL PASS: exact Std-only primitive closure and frozen evaluator bytes'

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
  if ($depth -ne 0 -or $quoted) { throw 'PRE1-BUILDER-FIREWALL unterminated comment/string' }
  return $out.ToString()
}

function Invoke-ContractGuard {
  $shell = (Get-Process -Id $PID).Path
  $guard = Join-Path $PSScriptRoot 'preprocessing_contract_firewall.ps1'
  # The child runs as an owned, bounded process with its own deadline, so a
  # standalone firewall invocation is bounded too (audit P3-7). Its stdout and
  # stderr lines are folded into one message; a timeout or output-limit hit is
  # inconclusive and fails.
  . (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
  $result = Invoke-RMQOwnedBoundedProcess -FilePath $shell `
    -Arguments @('-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', $guard) `
    -WorkingDirectory $pre1Root -Stage 'builder-firewall-contract-guard' `
    -DeadlineSeconds $ContractGuardDeadlineSeconds -OutputLimitBytes 1048576 `
    -TempRoot (Join-Path $pre1Root '.lake/preprocessing-builder-firewall')
  $lines = @($result.Output | ForEach-Object { [string]$_ })
  if ($result.TimedOut -or $result.OutputLimitExceeded) {
    throw ("PRE1-BUILDER-FIREWALL contract guard inconclusive: timeout=$($result.TimedOut), " +
      "outputLimit=$($result.OutputLimitExceeded) after $($result.DurationSeconds)s of $($ContractGuardDeadlineSeconds)s")
  }
  if ($result.ExitCode -ne 0 -or -not ($lines -ccontains $contractGuardPass)) {
    throw "PRE1-BUILDER-FIREWALL contract guard failed: $($lines -join ' | ')"
  }
}

function ConvertTo-ClosurePath([string]$module) {
  return 'RMQ/Core/WordRAM/Construction/' +
    $module.Substring($modulePrefix.Length).Replace('.', '/') + '.lean'
}

function Read-DirectImports([string]$relative) {
  $path = Join-Path $pre1Root $relative
  if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
    throw "PRE1-BUILDER-FIREWALL closure module missing: $relative"
  }
  $source = $utf8Strict.GetString([IO.File]::ReadAllBytes($path))
  $code = Remove-LeanComments $source
  $imports = @([regex]::Matches($code, '(?m)^\s*import\s+([^\r\n]+)') | ForEach-Object {
    $_.Groups[1].Value.Trim() -split '\s+'
  })
  # Any nonstandard header directive or import syntax is rejected, not
  # silently omitted. Lean's own compiler still validates the source.
  $remaining = [regex]::Replace($code, '(?m)^\s*import\s+[^\r\n]+', '')
  if ($remaining -match '\b(import|prelude)\b') {
    throw "PRE1-BUILDER-FIREWALL unrecognized import/header syntax: $relative"
  }
  return $imports
}

try {
  Invoke-ContractGuard

  $directImports = [ordered]@{}
  foreach ($relative in $allowedImports.Keys) {
    $imports = @(Read-DirectImports $relative)
    $expected = @($allowedImports[$relative])
    if ($imports.Count -ne $expected.Count -or
        (@(Compare-Object -CaseSensitive $imports $expected)).Count -ne 0 -or
        (@($imports | Select-Object -Unique)).Count -ne $imports.Count) {
      throw "PRE1-BUILDER-FIREWALL imports rejected: $relative actual=[$($imports -join ',')]"
    }
    $directImports[$relative] = $imports
  }

  # Every Lean file under Builder/ must be a table key; an unlisted module
  # cannot enter the closure unguarded.
  $builderRoot = Join-Path $pre1Root 'RMQ/Core/WordRAM/Construction/Builder'
  if (Test-Path -LiteralPath $builderRoot -PathType Container) {
    foreach ($file in [IO.Directory]::EnumerateFiles($builderRoot, '*.lean', [IO.SearchOption]::AllDirectories)) {
      $relative = $file.Substring($pre1Root.Length).TrimStart('\', '/').Replace('\', '/')
      if (-not $allowedImports.Contains($relative)) {
        throw "PRE1-BUILDER-FIREWALL unregistered closure module: $relative"
      }
    }
  }

  # Transitive closure from every table key. Each import must be Std, a table
  # key, or a contract root; anything else escapes the guarded closure.
  $visited = [Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  $queue = [Collections.Generic.Queue[string]]::new()
  foreach ($relative in $allowedImports.Keys) { $queue.Enqueue($relative) }
  while ($queue.Count -gt 0) {
    $relative = $queue.Dequeue()
    if (-not $visited.Add($relative)) { continue }
    foreach ($module in @($directImports[$relative])) {
      if ($module -ceq 'Std' -or $contractRoots -ccontains $module) { continue }
      if ($module.StartsWith($modulePrefix, [StringComparison]::Ordinal)) {
        $target = ConvertTo-ClosurePath $module
        if ($allowedImports.Contains($target)) { $queue.Enqueue($target); continue }
      }
      throw "PRE1-BUILDER-FIREWALL transitive closure escapes: $module via $relative"
    }
  }

  $manifestPath = Join-Path $pre1Root 'docs/internal/extensions/pre1/builder_manifest.json'
  $manifest = $utf8Strict.GetString([IO.File]::ReadAllBytes($manifestPath)) | ConvertFrom-Json
  if ($manifest.version -ne 1 -or @($manifest.files).Count -ne $allowedImports.Count) {
    throw 'PRE1-BUILDER-FIREWALL exact builder registry version/count'
  }
  $seen = @{}
  foreach ($entry in $manifest.files) {
    if (-not $allowedImports.Contains($entry.path) -or $seen.ContainsKey($entry.path)) {
      throw 'PRE1-BUILDER-FIREWALL duplicate/unknown closure path'
    }
    $seen[$entry.path] = $true
    $raw = [IO.File]::ReadAllBytes((Join-Path $pre1Root $entry.path))
    $normalized = $utf8Strict.GetString($raw).Replace("`r`n", "`n")
    $sha = [Security.Cryptography.SHA256]::Create()
    try { $actual = [BitConverter]::ToString($sha.ComputeHash($utf8Strict.GetBytes($normalized))).Replace('-', '') }
    finally { $sha.Dispose() }
    if ($actual -cne $entry.sha256) {
      throw "PRE1-BUILDER-FIREWALL frozen closure bytes changed: $($entry.path)"
    }
  }
  Write-Output "PRE1-BUILDER-FIREWALL PASS: layered closure over the contract guard, $($allowedImports.Count) modules"
  exit 0
} catch { Write-Output $_.Exception.Message; exit 1 }
