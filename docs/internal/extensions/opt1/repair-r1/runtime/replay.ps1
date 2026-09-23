#!/usr/bin/env pwsh
[CmdletBinding()]
param(
  [AllowEmptyString()][string]$OnlyCase,
  [switch]$SelectorProbeOnly,
  [string]$RepoRoot = ([IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../../..'))),
  [string]$ArtifactDirectory = ''
)
$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
$utf8 = [Text.UTF8Encoding]::new($false, $true)
$onlyBound = $PSBoundParameters.ContainsKey('OnlyCase')
$repoRoot = [IO.Path]::GetFullPath($RepoRoot)
$productionPath = Join-Path $repoRoot 'scripts/packed_optimized_runtime.ps1'
$registryFile = Join-Path $PSScriptRoot 'REGISTRY.json'
$expectedVersion = 'opt1-r1-runtime-v1'
# Independent pinned order; the data registry cannot silently lose or duplicate a case.
$expectedIDs = @(
  'R1RT-ACCEPT-STDOUT',
  'R1RT-ACCEPT-STDERR',
  'R1RT-ACCEPT-BLANK-SEPARATORS',
  'R1RT-MIXED-OUT-ERR',
  'R1RT-MIXED-ERR-OUT',
  'R1RT-MIXED-STDOUT',
  'R1RT-MIXED-STDERR',
  'R1RT-MIXED-BOTH',
  'R1RT-HOLDOUT-STDOUT',
  'R1RT-HOLDOUT-STDERR',
  'R1RT-UNRELATED-ONLY',
  'R1RT-DUPLICATE-STDOUT',
  'R1RT-DUPLICATE-STDERR',
  'R1RT-DUPLICATE-CROSS',
  'R1RT-WRONG-SURFACE',
  'R1RT-WRONG-CASE',
  'R1RT-WRONG-PREFIX',
  'R1RT-PAD-LEFT',
  'R1RT-PAD-RIGHT',
  'R1RT-WHITESPACE-EXTRA',
  'R1RT-BLANK-ONLY',
  'R1RT-NO-OUTPUT',
  'R1RT-SUCCESS-CASE',
  'R1RT-SUCCESS-SUMMARY',
  'R1RT-HOLDOUT-SUCCESS',
  'R1RT-RESOURCE-STACK',
  'R1RT-RESOURCE-HEARTBEATS',
  'R1RT-HOLDOUT-RESOURCE',
  'R1RT-RESOURCE-ONLY',
  'R1RT-EXIT-ZERO',
  'R1RT-EXIT-SEVEN',
  'R1RT-TIMEOUT-EXPECTED',
  'R1RT-TIMEOUT-ABSENT',
  'R1RT-OVERFLOW-EXPECTED',
  'R1RT-OVERFLOW-ABSENT',
  'R1RT-BOUNDARY-OMITTED',
  'R1RT-BOUNDARY-VALID',
  'R1RT-BOUNDARY-EMPTY',
  'R1RT-BOUNDARY-WHITESPACE',
  'R1RT-BOUNDARY-PADDED',
  'R1RT-BOUNDARY-MALFORMED',
  'R1RT-BOUNDARY-UNKNOWN',
  'R1RT-BOUNDARY-ZERO',
  'R1RT-BOUNDARY-DUPLICATE',
  'R1RT-BOUNDARY-CONTRADICTORY',
  'R1RT-BOUNDARY-SELECTOR-STARTUP',
  'R1RT-BOUNDARY-REGISTRY-SELFTEST',
  'R1RT-REGISTRY-LITERAL-POSITIVE',
  'R1RT-REGISTRY-LITERAL-MIDDLE-OMITTED',
  'R1RT-REGISTRY-LITERAL-MIDDLE-DUPLICATE',
  'R1RT-REGISTRY-MARKDOWN-MIDDLE-OMITTED',
  'R1RT-REGISTRY-SOURCE-MIDDLE-DUPLICATE',
  'R1RT-REGISTRY-SOURCE-POSITIVE')

function Assert-R1RuntimeExact([string[]]$Actual, [string[]]$Expected, [string]$Label) {
  if (@($Expected).Count -eq 0 -or @($Actual).Count -ne @($Expected).Count -or
      ($Actual -join "`n") -cne ($Expected -join "`n") -or
      @($Actual | Select-Object -Unique).Count -ne @($Actual).Count) {
    throw "OPT1-R1-REGISTRY: $Label missing, duplicated, extra, reordered or changed"
  }
}

function Invoke-R1RuntimeVerdict([scriptblock]$Action, [string]$Expected, [string]$Prefix) {
  $accepted = $true; $diagnostic = ''
  try { & $Action } catch { $accepted = $false; $diagnostic = $_.Exception.Message }
  if (($accepted -and $Expected -cne 'ACCEPT') -or
      (-not $accepted -and ($Expected -cne 'REJECT' -or -not $diagnostic.StartsWith($Prefix, [StringComparison]::Ordinal)))) {
    throw "OPT1-R1-VERDICT: expected=$Expected accepted=$accepted diagnostic=$diagnostic"
  }
  return [pscustomobject]@{ Accepted=$accepted; Diagnostic=$diagnostic }
}

function Write-R1RuntimeJson([string]$Path, [object]$Value) {
  [IO.File]::WriteAllText($Path, ($Value | ConvertTo-Json -Depth 20), $utf8)
}

function Get-R1RuntimeSnapshot {
  $hashes = [ordered]@{}
  foreach ($path in @($productionPath, (Join-Path $repoRoot 'scripts/owned_process_tree.ps1'),
      (Join-Path $repoRoot 'RMQ/Validation/PackedOptimized.lean'),
      (Join-Path $repoRoot 'docs/internal/extensions/opt1/runtime-replay/REGISTRY.md'),
      $registryFile, $PSCommandPath)) {
    $hashes[$path] = (Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant()
  }
  return $hashes
}

$records = [Collections.Generic.List[object]]::new()
$executed = [Collections.Generic.List[string]]::new()
$exitCode = 0; $before = $null; $selectedIDs = @(); $artifactRoot = $null
try {
  # Immutable repair-fixture bytes, pinned independently of the input document.
  # The local enumerated -text attribute preserves this new JSON on checkout.
  if ((Get-FileHash -LiteralPath $registryFile -Algorithm SHA256).Hash.ToLowerInvariant() -cne
      '35dee68d8efbb972fb35276bc03b1ec18071048d83e0bfac0334daa9364ade4d') {
    throw 'OPT1-R1-REGISTRY: frozen case definitions changed'
  }
  $registry = $utf8.GetString([IO.File]::ReadAllBytes($registryFile)) | ConvertFrom-Json
  if ($registry.Version -cne $expectedVersion -or $registry.ExpectedCount -ne 53) { throw 'OPT1-R1-REGISTRY: version/count mismatch' }
  Assert-R1RuntimeExact @($registry.Cases | ForEach-Object { $_.ID }) $expectedIDs 'runtime registry'
  if ($onlyBound) {
    if ([string]::IsNullOrWhiteSpace($OnlyCase)) { throw 'OPT1-R1-SELECTOR: explicitly empty selector' }
    if ($OnlyCase -cnotmatch '^R1RT-[A-Z][A-Z0-9-]*$') { throw 'OPT1-R1-SELECTOR: malformed selector' }
    if (-not ($expectedIDs -ccontains $OnlyCase)) { throw "OPT1-R1-SELECTOR: unknown selector $OnlyCase" }
    $selectedIDs = @($OnlyCase)
  } else { $selectedIDs = @($expectedIDs) }
  if ($SelectorProbeOnly) {
    Write-Host "OPT1-R1-RUNTIME SELECTOR PASS bound=$onlyBound selected=$($selectedIDs.Count) ids=$($selectedIDs -join ',')"
  } else {
    if ($ArtifactDirectory -ceq '') { $ArtifactDirectory = Join-Path $repoRoot ('.lake/opt1-r1-runtime/' + [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssZ') + '-' + [Guid]::NewGuid().ToString('N')) }
    $artifactRoot = [IO.Path]::GetFullPath($ArtifactDirectory)
    if (Test-Path -LiteralPath $artifactRoot) { throw "OPT1-R1-ARTIFACT: output directory already exists: $artifactRoot" }
    [void][IO.Directory]::CreateDirectory($artifactRoot)
    Write-Host "OPT1-R1-RUNTIME ARTIFACTS $artifactRoot"
    $before = Get-R1RuntimeSnapshot
    . (Join-Path $repoRoot 'scripts/owned_process_tree.ps1')
    # Load unique function AST extents from production. Never substitute a copied detector.
    $tokens = $null; $parseErrors = $null
    $ast = [Management.Automation.Language.Parser]::ParseFile($productionPath, [ref]$tokens, [ref]$parseErrors)
    if (@($parseErrors).Count -ne 0) { throw 'OPT1-R1-AST: production parse failed' }
    $functionNames = @('Assert-OPT1Bounded','Assert-OPT1Rejected','Assert-OPT1Exact','Read-OPT1Source','Assert-OPT1Registry')
    foreach ($functionName in $functionNames) {
      $definitions = @($ast.FindAll({ param($node) $node -is [Management.Automation.Language.FunctionDefinitionAst] -and $node.Name -ceq $functionName }, $true))
      if ($definitions.Count -ne 1) { throw "OPT1-R1-AST: missing/duplicate production function $functionName" }
      . ([scriptblock]::Create($definitions[0].Extent.Text))
    }
    foreach ($variableName in @('registryVersion','positiveIDs','negativeIDs','allIDs','runtimePath','registryPath')) {
      $assignments = @($ast.EndBlock.Statements | Where-Object {
        $_ -is [Management.Automation.Language.AssignmentStatementAst] -and $_.Left.Extent.Text -ceq ('$' + $variableName) })
      if ($assignments.Count -ne 1) { throw "OPT1-R1-AST: missing/duplicate production literal $variableName" }
      . ([scriptblock]::Create($assignments[0].Extent.Text))
    }
    $shellPath = (Get-Process -Id $PID).Path
    $expectedDiagnostic = 'uncaught exception: N01-JUMP: compiler observation mismatch'
    foreach ($id in $selectedIDs) {
      $case = @($registry.Cases | Where-Object { $_.ID -ceq $id })[0]
      $record = [ordered]@{ ID=$id; Kind=$case.Kind; Expected=$case.Expected; Result=$null; Verdict=$null; Restoration=$null }
      if ($case.Kind -ceq 'registry') {
        $prefix = if ($case.Expected -ceq 'REJECT') { 'OPT1-REGISTRY:' } else { '' }
        $action = switch ($case.Mode) {
          'literal-positive' { { Assert-OPT1Registry } }
          'literal-middle-omitted' { { Assert-OPT1Registry -Cases (@($allIDs[0..11]) + @($allIDs[13..26])) } }
          'literal-middle-duplicate' { { $changed = $allIDs.Clone(); $changed[12] = $changed[11]; Assert-OPT1Registry -Cases $changed } }
          'markdown-middle-omitted' { { $markdown = Read-OPT1Source $registryPath; Assert-OPT1Registry -Markdown $markdown.Replace('| C13-EMPTY-BRANCHES | ACCEPT | none |','') } }
          'source-middle-duplicate' { { $source = Read-OPT1Source $runtimePath; Assert-OPT1Registry -Source $source.Replace('"C12-INITIALLY-FAULTED", "C13-EMPTY-BRANCHES"','"C12-INITIALLY-FAULTED", "C12-INITIALLY-FAULTED"') } }
          'source-positive' { { Assert-OPT1Registry -Source (Read-OPT1Source $runtimePath) } }
          default { throw 'OPT1-R1-REGISTRY: unsupported mutation mode' }
        }
        $record.Verdict = Invoke-R1RuntimeVerdict $action $case.Expected $prefix
      } else {
        $fixture = Join-Path $artifactRoot ($id + '.ps1')
        $deadline = 60; $ceiling = 1048576
        $arguments = @('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',$fixture)
        $mutationPath = Join-Path $artifactRoot ($id + '.restored.bin')
        $rootPidPath = Join-Path $artifactRoot ($id + '.root.pid')
        $childPidPath = Join-Path $artifactRoot ($id + '.child.pid')
        $emissionPath = Join-Path $artifactRoot ($id + '.emitted.txt')
        $original = [byte[]]@(0,255,13,10,10,65,0,66)
        [IO.File]::WriteAllBytes($mutationPath, $original)
        $originalHash = (Get-FileHash -LiteralPath $mutationPath -Algorithm SHA256).Hash
        $text = "[IO.File]::WriteAllText('$($mutationPath.Replace("'", "''"))', 'changed by owned child')`n"
        if ($case.Kind -ceq 'classifier') {
          foreach ($line in @($case.Stdout)) { $text += "[Console]::Out.WriteLine('$($line.Replace("'", "''"))')`n" }
          foreach ($line in @($case.Stderr)) { $text += "[Console]::Error.WriteLine('$($line.Replace("'", "''"))')`n" }
          $text += "exit $($case.Exit)`n"
        } elseif ($case.Kind -in @('timeout','overflow')) {
          if ($case.EmitExpected) { $text += "[Console]::Out.WriteLine('$expectedDiagnostic')`n[Console]::Out.Flush()`n" }
          $emission = if ($case.EmitExpected) { 'expected diagnostic emitted and flushed' } else { 'no expected diagnostic emitted' }
          $text += "[IO.File]::WriteAllText('$($emissionPath.Replace("'", "''"))', '$emission')`n"
          if ($case.Kind -ceq 'timeout') {
            $deadline = 30
            $window = if (Test-RMQOwnedProcessWindows) { '-WindowStyle Hidden' } else { '' }
            $text += "[IO.File]::WriteAllText('$($rootPidPath.Replace("'", "''"))', [string]`$PID)`n"
            $text += "`$child = Start-Process -FilePath '$($shellPath.Replace("'", "''"))' -ArgumentList @('-NoProfile','-Command','Start-Sleep -Seconds 120') -PassThru $window`n"
            $text += "[IO.File]::WriteAllText('$($childPidPath.Replace("'", "''"))', [string]`$child.Id)`n"
          } else { $ceiling = 32768; $text += "[Console]::Error.WriteLine(('X' * 131072))`n" }
          $text += "Start-Sleep -Seconds 120`nexit 1`n"
        } elseif ($case.Kind -ceq 'boundary') {
          # Actual production entry with exact PowerShell parameter binding and an inherited selector.
          $text += "`$env:OPT1_RUNTIME_SELECTOR = 'id:R1-INHERITED-SELECTOR'`n"
          $invocation = switch ($case.Mode) {
            'omitted' { '-SelectorProbeOnly' }
            'valid' { "-SelectorProbeOnly -OnlyCase 'C01-ZERO-BRANCH'" }
            'empty' { "-OnlyCase ''" }
            'whitespace' { "-OnlyCase ' '" }
            'padded' { "-OnlyCase ' C01-ZERO-BRANCH '" }
            'malformed' { "-OnlyCase 'C01-ZERO-BRANCH,C02-NONZERO-BRANCH'" }
            'unknown' { "-OnlyCase 'C99-UNKNOWN'" }
            'zero' { "-OnlyCase '0'" }
            'duplicate' { "-OnlyCase 'C01-ZERO-BRANCH' -OnlyCase 'C02-NONZERO-BRANCH'" }
            'contradictory' { '-RegistrySelfTestOnly -SelectorProbeOnly' }
            'selector-startup' { "-OnlyCase 'C01-ZERO-BRANCH' -StartupOnly" }
            'registry-selftest' { '-RegistrySelfTestOnly' }
            default { throw 'OPT1-R1-REGISTRY: unsupported boundary mode' }
          }
          $call = "& '$($productionPath.Replace("'", "''"))' $invocation"
          if ($case.Mode -ceq 'duplicate') {
            $text += "try { $call; throw 'OPT1-R1-BOUNDARY: duplicate unexpectedly accepted' } catch [Management.Automation.ParameterBindingException] { [Console]::Error.WriteLine('OPT1-R1-BOUNDARY: duplicate parameter rejected'); `$global:LASTEXITCODE=1 }`n"
          } else { $text += $call + "`n" }
          $text += "`$code = [int]`$LASTEXITCODE`nif (`$env:OPT1_RUNTIME_SELECTOR -cne 'id:R1-INHERITED-SELECTOR') { throw 'OPT1-R1-BOUNDARY: selector environment was not restored' }`n[Console]::Out.WriteLine('OPT1-R1-BOUNDARY ENV RESTORED')`nexit `$code`n"
        } else { throw 'OPT1-R1-REGISTRY: unsupported case kind' }
        [IO.File]::WriteAllText($fixture, $text, $utf8)
        $result = $null
        try {
          $result = Invoke-RMQOwnedBoundedProcess -FilePath $shellPath -Arguments $arguments -WorkingDirectory $repoRoot -Stage $id -DeadlineSeconds $deadline -OutputLimitBytes $ceiling -TempRoot $artifactRoot
          $record.Result = $result
          $record['Command'] = @{ Executable=$shellPath; Arguments=$arguments; DeadlineSeconds=$deadline; OutputLimitBytes=$ceiling }
          if ($case.Kind -ceq 'boundary') {
            if ($result.TimedOut -or $result.OutputLimitExceeded) { throw "OPT1-R1-BOUNDARY: incomplete $id" }
            $wantedExit = if ($case.Expected -ceq 'ACCEPT') { 0 } else { 1 }
            $token = switch ($case.Mode) {
              'omitted' { 'OPT1-SELECTOR PROBE PASS bound=False selected=27 ids=' }
              'valid' { 'OPT1-SELECTOR PROBE PASS bound=True selected=1 ids=C01-ZERO-BRANCH' }
              'empty' { 'OPT1-SELECTOR: explicitly empty selector' }
              'whitespace' { 'OPT1-SELECTOR: explicitly empty selector' }
              'padded' { 'OPT1-SELECTOR: malformed selector' }
              'malformed' { 'OPT1-SELECTOR: malformed selector' }
              'unknown' { 'OPT1-SELECTOR: unknown selector C99-UNKNOWN' }
              'zero' { 'OPT1-SELECTOR: malformed selector' }
              'duplicate' { 'OPT1-R1-BOUNDARY: duplicate parameter rejected' }
              'contradictory' { 'OPT1-SELECTOR: incompatible modes' }
              'selector-startup' { 'OPT1-SELECTOR: incompatible modes' }
              'registry-selftest' { 'OPT1-REGISTRY SELF-TEST PASS expected=27 ' }
            }
            $outLines = @($result.StandardOutput)
            $errLines = @($result.StandardError)
            if ($result.ExitCode -ne $wantedExit -or @($outLines | Where-Object { $_ -ceq 'OPT1-R1-BOUNDARY ENV RESTORED' }).Count -ne 1) { throw "OPT1-R1-BOUNDARY: wrong exit/restoration $id" }
            if ($case.Expected -ceq 'REJECT') {
              if ($errLines.Count -ne 1 -or $errLines[0] -cne $token -or $outLines.Count -ne 1) { throw "OPT1-R1-BOUNDARY: wrong exact rejection $id" }
            } else {
              $expectedLine = if ($case.Mode -ceq 'omitted') { $token + ($allIDs -join ',') }
                elseif ($case.Mode -ceq 'registry-selftest') { $token + 'empty/missing/duplicate/extra/reordered/source/markdown/zero-executed/wrong-reject/timeout' } else { $token }
              if ($errLines.Count -ne 0 -or $outLines.Count -ne 2 -or $outLines[0] -cne $expectedLine) { throw "OPT1-R1-BOUNDARY: wrong exact acceptance $id" }
            }
            $record.Verdict = @{ BoundaryExit=$wantedExit; ExactDiagnostic=$token; EnvironmentRestored=$true; SemanticLaunches=0 }
          } else {
            if ($case.Kind -ceq 'classifier' -and ($result.TimedOut -or $result.OutputLimitExceeded)) { throw "OPT1-R1-SETUP: bounded child did not complete $id" }
            if ($case.Kind -ceq 'timeout' -and -not $result.TimedOut) { throw 'OPT1-R1-DEADLINE: intended timeout not created' }
            if ($case.Kind -ceq 'overflow' -and (-not $result.OutputLimitExceeded -or $result.TimedOut)) { throw 'OPT1-R1-DEADLINE: intended overflow not created independently' }
            if ($case.Kind -in @('timeout','overflow')) {
              if (-not (Test-Path -LiteralPath $emissionPath) -or [IO.File]::ReadAllText($emissionPath) -cne $emission) { throw 'OPT1-R1-DEADLINE: intended diagnostic-emission control not created' }
              if ($case.Kind -ceq 'timeout') {
                $hasExpected = @($result.StandardOutput | Where-Object { $_ -ceq $expectedDiagnostic }).Count -eq 1
                if ($hasExpected -ne $case.EmitExpected) { throw 'OPT1-R1-DEADLINE: intended retained diagnostic-presence control not created' }
              }
              $record['Emission'] = @{ ExpectedDiagnosticEmitted=$case.EmitExpected; Witness=[IO.File]::ReadAllText($emissionPath);
                CaptureLimit='Shared owned helper discards both retained streams on overflow; production receives its untouched result and rejects by OutputLimitExceeded before diagnostics' }
            }
            $record.Verdict = Invoke-R1RuntimeVerdict { Assert-OPT1Rejected $result 'N01-JUMP: compiler observation mismatch' } $case.Expected $case.Prefix
          }
        } finally {
          [IO.File]::WriteAllBytes($mutationPath, $original)
          $restoredHash = (Get-FileHash -LiteralPath $mutationPath -Algorithm SHA256).Hash
          if ($restoredHash -cne $originalHash) { throw 'OPT1-R1-RESTORATION: scratch bytes were not restored' }
          $record.Restoration = @{ BeforeSHA256=$originalHash; AfterSHA256=$restoredHash; ExactBytes=$true; TrackedMutations=0 }
          if ($case.Kind -ceq 'timeout') {
            if (-not (Test-Path -LiteralPath $rootPidPath) -or -not (Test-Path -LiteralPath $childPidPath)) { throw 'OPT1-R1-DEADLINE: INCONCLUSIVE actual descendant was not created' }
            $ownedIDs = @([int][IO.File]::ReadAllText($rootPidPath), [int][IO.File]::ReadAllText($childPidPath))
            $alive = @(Get-RMQAliveProcessIds $ownedIDs)
            if ($alive.Count -gt 0) { foreach ($ownedID in $alive) { Stop-Process -Id $ownedID -Force }; throw 'OPT1-R1-DEADLINE: owned descendant/root survived' }
            $record['Descendants'] = @{ Root=$ownedIDs[0]; Child=$ownedIDs[1]; Absent=$true; Host=[Environment]::OSVersion.Platform.ToString(); OtherHost='UNEXECUTED' }
          }
          Write-R1RuntimeJson (Join-Path $artifactRoot ($id + '.json')) $record
        }
      }
      $records.Add($record); $executed.Add($id)
      Write-Host "OPT1-R1-RUNTIME CASE $id PASS"
    }
    Assert-R1RuntimeExact @($executed) $selectedIDs 'executed runtime registry'
  }
} catch {
  $exitCode = 1
  [Console]::Error.WriteLine($_.Exception.Message)
} finally {
  if ($null -ne $before) {
    $after = Get-R1RuntimeSnapshot
    if (($before | ConvertTo-Json -Compress) -cne ($after | ConvertTo-Json -Compress)) { $exitCode=1; [Console]::Error.WriteLine('OPT1-R1-RESTORATION: production/source/registry/runner bytes changed') }
    Write-R1RuntimeJson (Join-Path $artifactRoot 'RESULT.json') @{ Version=$expectedVersion; SourceBefore=$before; SourceAfter=$after; Expected=$selectedIDs; Executed=@($executed); ExitCode=$exitCode; Cases=@($records); TrackedMutations=0; POSIX='UNEXECUTED'; Meaning='Host production-classifier and boundary controls; not Lean semantic execution' }
  }
}
if ($exitCode -eq 0 -and -not $SelectorProbeOnly) { Write-Host "OPT1-R1-RUNTIME PASS executed=$($executed.Count) expected=$($selectedIDs.Count) registry=$expectedVersion" }
exit $exitCode
