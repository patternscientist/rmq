#!/usr/bin/env pwsh
[CmdletBinding()]
param(
  [Parameter(Mandatory=$true)][ValidatePattern('^RMQ\.[A-Za-z0-9_.]+$')][string]$Module,
  [ValidateRange(10,7200)][int]$DeadlineSeconds = 1800,
  [string]$LeanPath = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe',
  [switch]$PlanOnly
)
$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
$repo = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$cache = Join-Path $repo '.lake/build/lib/lean'
$tempRoot = Join-Path $repo '.lake/lb1-owned'
$evidence = Join-Path $repo 'docs/internal/extensions/lb1/evidence'
$utf8 = [Text.UTF8Encoding]::new($false, $true)
$seen = @{}
$visiting = @{}
$dependencies = @{}
$order = [Collections.Generic.List[string]]::new()
function Get-LB1LeanCode([string]$text) {
  # Ignore nested Lean comments and string literals while preserving line starts.
  $buffer = [Text.StringBuilder]::new()
  $depth = 0
  $quoted = $false
  $lineComment = $false
  $lineStart = 0
  for ($i=0; $i -lt $text.Length; $i++) {
    $c = $text[$i]
    $pair = if ($i+1 -lt $text.Length) { $text.Substring($i,2) } else { '' }
    if ($c -eq "`n") {
      $line = $buffer.ToString($lineStart,$buffer.Length-$lineStart).Trim()
      [void]$buffer.Append($c); $lineStart=$buffer.Length; $lineComment=$false
      # Lean imports belong to the module header. Stop at its first command;
      # this avoids scanning enormous proof bodies and quoted sample imports.
      if ($depth -eq 0 -and -not $quoted -and $line -ne '' -and
          $line -notmatch '^import\s' -and $line -cne 'prelude') { break }
      continue
    }
    if ($lineComment) { [void]$buffer.Append(' '); continue }
    if ($depth -gt 0) {
      if ($pair -ceq '/-') { $depth++; $i++ }
      elseif ($pair -ceq '-/') { $depth--; $i++ }
      [void]$buffer.Append(' '); continue
    }
    if ($quoted) {
      if ($c -eq '\') { $i++ }
      elseif ($c -eq '"') { $quoted=$false }
      [void]$buffer.Append(' '); continue
    }
    if ($pair -ceq '/-') { $depth=1; $i++; [void]$buffer.Append(' '); continue }
    if ($pair -ceq '--') { $lineComment=$true; $i++; [void]$buffer.Append(' '); continue }
    if ($c -eq '"') { $quoted=$true; [void]$buffer.Append(' '); continue }
    [void]$buffer.Append($c)
  }
  if ($depth -ne 0 -or $quoted) { throw 'Unterminated Lean comment or string' }
  return $buffer.ToString()
}
function Visit-LB1Module([string]$name) {
  if ($seen.ContainsKey($name)) { return }
  if ($visiting.ContainsKey($name)) { throw "Import cycle at $name" }
  $sourcePath = Join-Path $repo ($name.Replace('.','/') + '.lean')
  if (-not (Test-Path -LiteralPath $sourcePath)) {
    if ($name.StartsWith('RMQ.')) { throw "Missing repository import $name" }
    return
  }
  $visiting[$name] = $true
  $text = Get-LB1LeanCode ([IO.File]::ReadAllText($sourcePath,$utf8))
  $direct = [Collections.Generic.List[string]]::new()
  foreach ($match in [regex]::Matches($text,'(?m)^import[ \t]+([^\r\n]+)')) {
    $imports = ($match.Groups[1].Value -split '--',2)[0].Trim() -split '\s+'
    foreach ($import in $imports) {
      if ($import -notmatch '^[A-Za-z0-9_.]+$') { throw "Unsupported import token: $import" }
      Visit-LB1Module $import
      if ($seen.ContainsKey($import)) { $direct.Add($import) }
    }
  }
  $visiting.Remove($name)
  $seen[$name] = $true
  $dependencies[$name] = $direct.ToArray()
  $order.Add($name)
}
Visit-LB1Module $Module
if ($PlanOnly) { $order; "LB1-BUILD-PLAN count=$($order.Count) target=$Module"; exit 0 }
foreach ($dir in @($cache,$tempRoot,$evidence)) { [void][IO.Directory]::CreateDirectory($dir) }
$lean = [IO.Path]::GetFullPath($LeanPath)
if (-not (Test-Path -LiteralPath $lean -PathType Leaf)) { throw "Lean binary unavailable: $lean" }
$runId = [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')
$versionResult = Invoke-RMQOwnedBoundedProcess -FilePath $lean -Arguments @('--version') -WorkingDirectory $repo -Stage 'lean-version' -DeadlineSeconds 60 -OutputLimitBytes 1048576 -TempRoot $tempRoot
[IO.File]::WriteAllText((Join-Path $evidence ("version-$runId.json")),($versionResult|ConvertTo-Json -Depth 8),$utf8)
$version = ($versionResult.StandardOutput -join [Environment]::NewLine).Trim()
if ($versionResult.TimedOut -or $versionResult.OutputLimitExceeded -or $versionResult.ExitCode -ne 0 -or $version -notmatch 'version 4\.22\.0,') { throw "Unavailable/wrong pinned Lean: $version" }
$logPath = Join-Path $evidence ("build-$runId.jsonl")
$keys = @{}
$rebuilt = 0
foreach ($name in $order) {
  $relative = $name.Replace('.','/')
  $sourcePath = Join-Path $repo ($relative + '.lean')
  $outputPath = Join-Path $cache ($relative + '.olean')
  $keyPath = $outputPath + '.lb1-key'
  $hash = (Get-FileHash -LiteralPath $sourcePath -Algorithm SHA256).Hash
  # Each key includes the complete transitive source identity through direct imports.
  $dependencyKeys = @($dependencies[$name] | ForEach-Object { $keys[$_] }) -join ''
  $sha = [Security.Cryptography.SHA256]::Create()
  try { $key = [Convert]::ToHexString($sha.ComputeHash($utf8.GetBytes($version + $name + $hash + $dependencyKeys))) }
  finally { $sha.Dispose() }
  $keys[$name] = $key
  if ((Test-Path -LiteralPath $outputPath) -and (Test-Path -LiteralPath $keyPath) -and
      [IO.File]::ReadAllText($keyPath,$utf8) -ceq $key) {
    Write-Host "LB1-CACHED $name"
    continue
  }
  [void][IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($outputPath))
  Write-Host "LB1-BUILD $name deadline=$DeadlineSeconds"
  $started = [DateTime]::UtcNow.ToString('o')
  $arguments = @('-j1','-o',$outputPath,$sourcePath)
  $result = Invoke-RMQOwnedBoundedProcess -FilePath $lean -Arguments $arguments -WorkingDirectory $repo -Stage $name -DeadlineSeconds $DeadlineSeconds -OutputLimitBytes 4194304 -TempRoot $tempRoot -Environment @{ LEAN_PATH=$cache }
  $record = [ordered]@{ Module=$name; SourceSHA256=$hash; CacheKey=$key; UTC=$started; Command=@($lean)+$arguments; Platform=[Environment]::OSVersion.ToString(); Result=$result }
  [IO.File]::AppendAllText($logPath,($record|ConvertTo-Json -Depth 10 -Compress)+[Environment]::NewLine,$utf8)
  foreach ($line in $result.Output) { Write-Host $line }
  if ($result.TimedOut -or $result.OutputLimitExceeded -or $result.ExitCode -ne 0) {
    throw "LB1 build incomplete: $name; exit=$($result.ExitCode), timeout=$($result.TimedOut); evidence=$logPath"
  }
  [IO.File]::WriteAllText($keyPath,$key,$utf8)
  $rebuilt++
}
Write-Host "LB1-BUILD-PASS target=$Module closure=$($order.Count) rebuilt=$rebuilt evidence=$logPath"
