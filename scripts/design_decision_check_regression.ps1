#!/usr/bin/env pwsh

[CmdletBinding()]
param()

$ErrorActionPreference = "Stop"

$callerRoot = [System.IO.Path]::GetFullPath((Get-Location).Path)
$productionPath = [System.IO.Path]::GetFullPath(
  (Join-Path $callerRoot "scripts/design_decision_check.ps1")
)
$regressionPath = [System.IO.Path]::GetFullPath(
  (Join-Path $callerRoot "scripts/design_decision_check_regression.ps1")
)
$gatePath = [System.IO.Path]::GetFullPath((Join-Path $callerRoot "scripts/gate.ps1"))
$shellPath = (Get-Process -Id $PID).Path
$gitTimeoutMs = 15000
$productionTimeoutMs = 30000
$failures = 0

if (-not (Test-Path -LiteralPath $productionPath -PathType Leaf)) {
  Write-Host "DESIGN-CHECK-REGRESSION: FAIL production checker not found: $productionPath"
  exit 1
}

function Stop-OwnedProcessTree {
  param([System.Diagnostics.Process]$Process)

  if ($null -eq $Process -or $Process.HasExited) {
    return $true
  }

  if ($env:OS -eq "Windows_NT") {
    $all = @(Get-CimInstance Win32_Process -ErrorAction SilentlyContinue)
    $pending = @([int]$Process.Id)
    $owned = @()
    while ($pending.Count -gt 0) {
      $parent = $pending[0]
      $pending = @($pending | Select-Object -Skip 1)
      $children = @($all | Where-Object { [int]$_.ParentProcessId -eq $parent })
      foreach ($child in $children) {
        $pending += [int]$child.ProcessId
        $owned += [int]$child.ProcessId
      }
    }
    [array]::Reverse($owned)
    foreach ($id in @($owned + [int]$Process.Id)) {
      Stop-Process -Id $id -Force -ErrorAction SilentlyContinue
    }
  } else {
    Stop-Process -Id $Process.Id -Force -ErrorAction SilentlyContinue
  }

  $null = $Process.WaitForExit(5000)
  return $Process.HasExited
}

function Invoke-BoundedProcess {
  param(
    [string]$FilePath,
    [string[]]$Arguments,
    [string]$WorkingDirectory,
    [int]$TimeoutMs
  )

  if ($TimeoutMs -le 0) {
    throw "positive subprocess deadline required"
  }

  $argumentText = @(
    foreach ($argument in $Arguments) {
      if ($argument -match '[\s"]') {
        '"' + $argument.Replace('"', '\"') + '"'
      } else {
        $argument
      }
    }
  ) -join " "
  $startInfo = [System.Diagnostics.ProcessStartInfo]::new()
  $startInfo.FileName = $FilePath
  $startInfo.Arguments = $argumentText
  $startInfo.WorkingDirectory = $WorkingDirectory
  $startInfo.UseShellExecute = $false
  $startInfo.CreateNoWindow = $true
  $startInfo.RedirectStandardOutput = $true
  $startInfo.RedirectStandardError = $true
  $process = $null
  try {
    $process = [System.Diagnostics.Process]::new()
    $process.StartInfo = $startInfo
    if (-not $process.Start()) {
      throw "failed to start bounded subprocess: $FilePath"
    }
    $stdoutTask = $process.StandardOutput.ReadToEndAsync()
    $stderrTask = $process.StandardError.ReadToEndAsync()
    $completed = $process.WaitForExit($TimeoutMs)
    $timedOut = -not $completed
    $cleaned = $true
    if ($timedOut) {
      $cleaned = Stop-OwnedProcessTree -Process $process
    } else {
      $process.WaitForExit()
    }
    $stdout = $stdoutTask.GetAwaiter().GetResult()
    $stderr = $stderrTask.GetAwaiter().GetResult()
    $output = @(($stdout + [Environment]::NewLine + $stderr) -split "\r?\n" |
        Where-Object { $_ })
    $code = if ($timedOut) { 124 } else { [int]$process.ExitCode }
    return [PSCustomObject]@{
      Code = $code
      TimedOut = $timedOut
      Cleaned = $cleaned
      Output = @($output | ForEach-Object { [string]$_ })
    }
  } finally {
    if ($null -ne $process -and -not $process.HasExited) {
      $null = Stop-OwnedProcessTree -Process $process
    }
    if ($null -ne $process) {
      $process.Dispose()
    }
  }
}

function Invoke-BoundedGit {
  param(
    [string[]]$Arguments,
    [string]$WorkingDirectory
  )

  $result = Invoke-BoundedProcess -FilePath "git" -Arguments $Arguments `
    -WorkingDirectory $WorkingDirectory -TimeoutMs $gitTimeoutMs
  if ($result.TimedOut -or -not $result.Cleaned -or $result.Code -ne 0) {
    throw "git $($Arguments -join ' ') failed with exit $($result.Code): $($result.Output -join '; ')"
  }
  return @($result.Output)
}

function Get-CallerSnapshot {
  $status = @(Invoke-BoundedGit -WorkingDirectory $callerRoot -Arguments @(
      "-c", "core.excludesfile=", "-c", "core.autocrlf=false",
      "status", "--porcelain=v1", "--untracked-files=all"
    ))
  $worktree = @(Invoke-BoundedGit -WorkingDirectory $callerRoot -Arguments @(
      "-c", "core.excludesfile=", "-c", "core.autocrlf=false",
      "diff", "--raw", "--no-ext-diff", "--"
    ))
  $index = @(Invoke-BoundedGit -WorkingDirectory $callerRoot -Arguments @(
      "-c", "core.excludesfile=", "-c", "core.autocrlf=false",
      "diff", "--cached", "--raw", "--no-ext-diff", "--"
    ))
  $hashes = @(
    foreach ($path in @($productionPath, $regressionPath, $gatePath)) {
      if (Test-Path -LiteralPath $path -PathType Leaf) {
        "$path=$((Get-FileHash -Algorithm SHA256 -LiteralPath $path).Hash)"
      }
    }
  )
  return @(
    "status:"
    $status
    "worktree:"
    $worktree
    "index:"
    $index
    "hashes:"
    $hashes
  ) -join [Environment]::NewLine
}

function Write-FixtureFile {
  param(
    [string]$Root,
    [string]$RelativePath,
    [string]$Content,
    [switch]$Append
  )

  $fullPath = Join-Path $Root $RelativePath
  [System.IO.Directory]::CreateDirectory((Split-Path -Parent $fullPath)) | Out-Null
  if ($Append) {
    [System.IO.File]::AppendAllText($fullPath, $Content + [Environment]::NewLine)
  } else {
    [System.IO.File]::WriteAllText($fullPath, $Content + [Environment]::NewLine)
  }
}

function Remove-FixtureTree {
  param([string]$Path)

  if (-not [System.IO.Directory]::Exists($Path)) {
    return
  }
  Get-ChildItem -LiteralPath $Path -Recurse -Force -ErrorAction SilentlyContinue |
    ForEach-Object { $_.Attributes = [System.IO.FileAttributes]::Normal }
  [System.IO.Directory]::Delete($Path, $true)
}

function Test-SubprocessDeadlineControl {
  $result = Invoke-BoundedProcess -FilePath $shellPath `
    -Arguments @("-NoLogo", "-NoProfile", "-Command", "Start-Sleep -Seconds 5") `
    -WorkingDirectory $callerRoot -TimeoutMs 200
  if (-not $result.TimedOut -or -not $result.Cleaned) {
    Write-Host "DESIGN-CHECK-REGRESSION: FAIL [subprocess-deadline-sleeper-control]"
    $script:failures += 1
    return
  }
  Write-Host "DESIGN-CHECK-REGRESSION: PASS [subprocess-deadline-sleeper-control] timeout classified and owned process cleaned"
}

$cases = @(
  @{ Id = "strict-missing-base"; Files = @{ "RMQ/New/StrictBaseProbe.lean" = "def strictBaseProbe := true" }; OmitBase = $true; Reject = $true; Output = "strict certification requires -Base" },
  @{ Id = "unenumerated-rmq-lean-path"; Files = @{ "RMQ/New/PreviouslyUnlisted.lean" = "def previouslyUnlisted := true" }; Reject = $true; Output = "code/public/repository-sensitive" },
  @{ Id = "new-validation-path"; Files = @{ "RMQ/Validation/NewPolicyProbe.lean" = "def newPolicyProbe := true" }; Reject = $true; Output = "code/public/repository-sensitive" },
  @{ Id = "new-workflow-script"; Files = @{ "scripts/new_workflow_probe.ps1" = "Write-Host probe" }; Reject = $true; Output = "workflow/process-sensitive" },
  @{ Id = "ordinary-public-doc"; Files = @{ "docs/NEW_PUBLIC_NOTE.md" = "# Public note" }; Reject = $true; Output = "code/public/repository-sensitive" },
  @{ Id = "unknown-repository-path-default-sensitive"; Files = @{ "new-format/data.policy" = "policy" }; Reject = $true; Output = "code/public/repository-sensitive" },
  @{ Id = "missing-code-decision"; Files = @{ "lakefile.toml" = "name = 'probe'" }; Reject = $true; Output = "update docs/internal/DESIGN_DECISIONS.md" },
  @{ Id = "missing-workflow-decision"; Files = @{ ".agents/new_policy/README.md" = "workflow" }; Reject = $true; Output = "update docs/internal/WORKFLOW_DESIGN_DECISIONS.md" },
  @{ Id = "p1-neutral-evidence-path-cannot-shadow-code-or-current-surface"; Files = @{ "docs/internal/audit_reports/P1NeutralBypass.lean" = "def p1NeutralBypass := true"; "docs/digests/PROJECT_DIGESTION_CURRENT_V2.md" = "# Unregistered current surface" }; Reject = $true; Output = "code/public/repository-sensitive" },
  @{ Id = "p1-neutral-audit-report-ps1-rejected"; Files = @{ "docs/internal/audit_reports/P1NeutralBypass.ps1" = "Write-Host bypass" }; Reject = $true; Output = "workflow/process-sensitive" },
  @{ Id = "p1-neutral-digest-code-rejected"; Files = @{ "docs/digests/P1NeutralBypass.ps1" = "Write-Host bypass" }; Reject = $true; Output = "workflow/process-sensitive" },
  @{ Id = "p1-current-looking-digest-heldout-rejected"; Files = @{ "docs/digests/RMQ_CURRENT_STATUS.md" = "# Unregistered current status" }; Reject = $true; Output = "code/public/repository-sensitive" },
  @{ Id = "p1-registered-current-digest-remains-sensitive"; Files = @{ "docs/digests/PROJECT_DIGESTION_CURRENT.md" = "# Registered current surface" }; Reject = $true; Output = "code/public/repository-sensitive" },
  @{ Id = "present-code-decision"; Files = @{ "RMQ/New/WithDecision.lean" = "def withDecision := true" }; CodeDecision = $true; Reject = $false; Output = "checked" },
  @{ Id = "present-workflow-decision"; Files = @{ "scripts/with_decision.ps1" = "Write-Host governed" }; WorkflowDecision = $true; Reject = $false; Output = "checked" },
  @{ Id = "present-correct-decisions"; Files = @{ "RMQ/New/BothDecisions.lean" = "def bothDecisions := true"; "scripts/both_decisions.ps1" = "Write-Host governed" }; CodeDecision = $true; WorkflowDecision = $true; Reject = $false; Output = "checked" },
  @{ Id = "neutral-worklog"; Files = @{ "docs/internal/NEW_POLICY_WORKLOG.md" = "# Evidence" }; Reject = $false; Output = "only neutral decision/evidence/history/report paths" },
  @{ Id = "neutral-audit-report"; Files = @{ "docs/internal/audit_reports/2026-07-19_probe.md" = "# Audit evidence" }; Reject = $false; Output = "only neutral decision/evidence/history/report paths" },
  @{ Id = "neutral-historical-digest"; Files = @{ "docs/digests/PROJECT_STATE_2026_07_19.md" = "# Frozen history" }; Reject = $false; Output = "only neutral decision/evidence/history/report paths" },
  @{ Id = "p1-neutral-audit-markdown-control"; Files = @{ "docs/internal/audit_reports/P1NeutralEvidence.md" = "# Audit evidence" }; Reject = $false; Output = "only neutral decision/evidence/history/report paths" },
  @{ Id = "p1-frozen-historical-digest-control"; Files = @{ "docs/digests/DEEP_PROJECT_DIGESTION_2026_07_19.md" = "# Frozen history" }; Reject = $false; Output = "only neutral decision/evidence/history/report paths" },
  @{ Id = "decision-logs-nonrecursive"; Files = @{}; CodeDecision = $true; WorkflowDecision = $true; Reject = $false; Output = "only neutral decision/evidence/history/report paths" },
  @{ Id = "nonstrict-local-worktree-mode"; Files = @{ "RMQ/New/LocalAdvisory.lean" = "def localAdvisory := true" }; NonStrict = $true; OmitBase = $true; Reject = $false; Output = "code/public/repository-sensitive" },
  @{ Id = "absolute-windows-repository-root"; Files = @{ "another-new-root/path.data" = "data" }; Reject = $true; Output = "code/public/repository-sensitive"; RequireDriveRoot = $true },
  @{ Id = "strict-unresolvable-base"; Files = @{ "RMQ/New/BadBase.lean" = "def badBase := true" }; BaseOverride = "not-a-real-base"; Reject = $true; Output = "could not resolve base" }
)

$expectedCaseIds = @(
  "strict-missing-base",
  "unenumerated-rmq-lean-path",
  "new-validation-path",
  "new-workflow-script",
  "ordinary-public-doc",
  "unknown-repository-path-default-sensitive",
  "missing-code-decision",
  "missing-workflow-decision",
  "p1-neutral-evidence-path-cannot-shadow-code-or-current-surface",
  "p1-neutral-audit-report-ps1-rejected",
  "p1-neutral-digest-code-rejected",
  "p1-current-looking-digest-heldout-rejected",
  "p1-registered-current-digest-remains-sensitive",
  "present-code-decision",
  "present-workflow-decision",
  "present-correct-decisions",
  "neutral-worklog",
  "neutral-audit-report",
  "neutral-historical-digest",
  "p1-neutral-audit-markdown-control",
  "p1-frozen-historical-digest-control",
  "decision-logs-nonrecursive",
  "nonstrict-local-worktree-mode",
  "absolute-windows-repository-root",
  "strict-unresolvable-base"
)

$expectedRejectCaseIds = @(
  "strict-missing-base",
  "unenumerated-rmq-lean-path",
  "new-validation-path",
  "new-workflow-script",
  "ordinary-public-doc",
  "unknown-repository-path-default-sensitive",
  "missing-code-decision",
  "missing-workflow-decision",
  "p1-neutral-evidence-path-cannot-shadow-code-or-current-surface",
  "p1-neutral-audit-report-ps1-rejected",
  "p1-neutral-digest-code-rejected",
  "p1-current-looking-digest-heldout-rejected",
  "p1-registered-current-digest-remains-sensitive",
  "absolute-windows-repository-root",
  "strict-unresolvable-base"
)

function Test-CaseRegistry {
  param([object[]]$Registry)

  $ids = @($Registry | ForEach-Object { [string]$_.Id })
  if ($ids.Count -ne $expectedCaseIds.Count -or
      @($ids | Group-Object | Where-Object Count -ne 1).Count -ne 0) {
    return $false
  }
  for ($i = 0; $i -lt $expectedCaseIds.Count; $i += 1) {
    if ($ids[$i] -ne $expectedCaseIds[$i]) {
      return $false
    }
  }
  $rejectIds = @($Registry | Where-Object { [bool]$_.Reject } |
      ForEach-Object { [string]$_.Id })
  if ($rejectIds.Count -ne $expectedRejectCaseIds.Count) {
    return $false
  }
  for ($i = 0; $i -lt $expectedRejectCaseIds.Count; $i += 1) {
    if ($rejectIds[$i] -ne $expectedRejectCaseIds[$i]) {
      return $false
    }
  }
  return $true
}

function Copy-CaseRegistry {
  param([object[]]$Registry)

  return @(
    foreach ($case in $Registry) {
      $copy = @{}
      foreach ($key in $case.Keys) {
        $copy[$key] = $case[$key]
      }
      $copy
    }
  )
}

if (-not (Test-CaseRegistry -Registry $cases)) {
  Write-Host "DESIGN-CHECK-REGRESSION: FAIL [exact-case-registry]"
  exit 1
}

$duplicateCases = @(Copy-CaseRegistry -Registry $cases) + @((Copy-CaseRegistry -Registry @($cases[0]))[0])
if (Test-CaseRegistry -Registry $duplicateCases) {
  Write-Host "DESIGN-CHECK-REGRESSION: FAIL [duplicate-case-id-control]"
  exit 1
}
Write-Host "DESIGN-CHECK-REGRESSION: PASS [duplicate-case-id-control] REJECT"

$missingCases = @($cases | Where-Object { [string]$_.Id -ne $expectedCaseIds[10] })
if (Test-CaseRegistry -Registry $missingCases) {
  Write-Host "DESIGN-CHECK-REGRESSION: FAIL [missing-required-case-control]"
  exit 1
}
Write-Host "DESIGN-CHECK-REGRESSION: PASS [missing-required-case-control] REJECT"

$verdictDriftCases = Copy-CaseRegistry -Registry $cases
$verdictDriftCases[0].Reject = -not [bool]$verdictDriftCases[0].Reject
if (Test-CaseRegistry -Registry $verdictDriftCases) {
  Write-Host "DESIGN-CHECK-REGRESSION: FAIL [case-verdict-drift-control]"
  exit 1
}
Write-Host "DESIGN-CHECK-REGRESSION: PASS [case-verdict-drift-control] REJECT"
Write-Host "DESIGN-CHECK-REGRESSION: PASS [exact-case-registry] $($cases.Count) ordered cases"

$gateText = Get-Content -Raw -LiteralPath $gatePath
$designInvocationPattern = '(?m)^\s*& "\$PSScriptRoot\\design_decision_check_regression\.ps1"\s*$'
$claimInvocationPattern = '(?m)^\s*& "\$PSScriptRoot\\claim_drift_policy_regression\.ps1"\s*$'
$designPropagationPattern = '(?ms)& "\$PSScriptRoot\\design_decision_check_regression\.ps1"\s*\r?\nif \(\$LASTEXITCODE -ne 0\) \{ Fail "design_decision_check_regression\.ps1 found issues" \}'
if ([regex]::Matches($gateText, $designInvocationPattern).Count -ne 1 -or
    [regex]::Matches($gateText, $claimInvocationPattern).Count -ne 1 -or
    -not [regex]::IsMatch($gateText, $designPropagationPattern)) {
  Write-Host "DESIGN-CHECK-REGRESSION: FAIL [aggregate-gate-wiring]"
  exit 1
}
Write-Host "DESIGN-CHECK-REGRESSION: PASS [aggregate-gate-wiring] exact-once invocations and immediate design-regression exit propagation"

$fixtureRoot = Join-Path ([System.IO.Path]::GetTempPath()) (
  "design-decision-check-regression-" + [Guid]::NewGuid().ToString("N")
)
$seedRoot = Join-Path $fixtureRoot "seed"
$baselineSnapshot = Get-CallerSnapshot
$rejectCount = 0
$acceptCount = 0

try {
  Test-SubprocessDeadlineControl

  [System.IO.Directory]::CreateDirectory($seedRoot) | Out-Null
  $null = Invoke-BoundedGit -WorkingDirectory $seedRoot -Arguments @("init", "-q")
  $null = Invoke-BoundedGit -WorkingDirectory $seedRoot -Arguments @("config", "user.email", "p1-regression@example.invalid")
  $null = Invoke-BoundedGit -WorkingDirectory $seedRoot -Arguments @("config", "user.name", "P1 Regression")
  Write-FixtureFile -Root $seedRoot -RelativePath "seed.txt" -Content "seed"
  Write-FixtureFile -Root $seedRoot -RelativePath "docs/internal/DESIGN_DECISIONS.md" -Content "# Code decisions"
  Write-FixtureFile -Root $seedRoot -RelativePath "docs/internal/WORKFLOW_DESIGN_DECISIONS.md" -Content "# Workflow decisions"
  $null = Invoke-BoundedGit -WorkingDirectory $seedRoot -Arguments @("-c", "core.autocrlf=false", "add", "--", ".")
  $null = Invoke-BoundedGit -WorkingDirectory $seedRoot -Arguments @("commit", "-q", "-m", "fixture base")
  $fixtureBase = [string]@(Invoke-BoundedGit -WorkingDirectory $seedRoot -Arguments @("rev-parse", "HEAD"))[0]
  if ($fixtureBase -notmatch "^[0-9a-f]{40}$") {
    throw "fixture base is not a 40-character commit: $fixtureBase"
  }

  foreach ($case in $cases) {
    $caseRoot = Join-Path $fixtureRoot ("case-" + [string]$case.Id)
    Copy-Item -LiteralPath $seedRoot -Destination $caseRoot -Recurse
    try {
      foreach ($entry in $case.Files.GetEnumerator()) {
        Write-FixtureFile -Root $caseRoot -RelativePath ([string]$entry.Key) -Content ([string]$entry.Value)
      }
      if ([bool]$case.CodeDecision) {
        Write-FixtureFile -Root $caseRoot -RelativePath "docs/internal/DESIGN_DECISIONS.md" `
          -Content ("Decision for " + [string]$case.Id) -Append
      }
      if ([bool]$case.WorkflowDecision) {
        Write-FixtureFile -Root $caseRoot -RelativePath "docs/internal/WORKFLOW_DESIGN_DECISIONS.md" `
          -Content ("Decision for " + [string]$case.Id) -Append
      }

      if ([bool]$case.RequireDriveRoot -and $env:OS -eq "Windows_NT" -and
          $caseRoot -notmatch "^[A-Za-z]:[\\/]") {
        Write-Host "DESIGN-CHECK-REGRESSION: FAIL [$($case.Id)] root is not drive-qualified: $caseRoot"
        $failures += 1
        continue
      }

      $arguments = @("-NoLogo", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", $productionPath)
      if (-not [bool]$case.NonStrict) {
        $arguments += "-Strict"
      }
      if (-not [bool]$case.OmitBase) {
        $baseArgument = if ($case.ContainsKey("BaseOverride")) {
          [string]$case.BaseOverride
        } else {
          $fixtureBase
        }
        $arguments += @("-Base", $baseArgument)
      }

      $result = Invoke-BoundedProcess -FilePath $shellPath -Arguments $arguments `
        -WorkingDirectory $caseRoot -TimeoutMs $productionTimeoutMs
      $joinedOutput = $result.Output -join [Environment]::NewLine
      $expectedCode = if ([bool]$case.Reject) { "nonzero" } else { "zero" }
      $passed = -not $result.TimedOut -and $result.Cleaned
      if ([bool]$case.Reject) {
        $passed = $passed -and $result.Code -ne 0
        $rejectCount += 1
      } else {
        $passed = $passed -and $result.Code -eq 0
        $acceptCount += 1
      }
      $passed = $passed -and $joinedOutput -match [regex]::Escape([string]$case.Output)
      if (-not $passed) {
        Write-Host "DESIGN-CHECK-REGRESSION: FAIL [$($case.Id)] expected exit $expectedCode and output '$($case.Output)'"
        $result.Output | ForEach-Object { Write-Host "  $_" }
        $failures += 1
      } else {
        $verdict = if ([bool]$case.Reject) { "REJECT" } else { "ACCEPT" }
        Write-Host "DESIGN-CHECK-REGRESSION: PASS [$($case.Id)] $verdict"
      }
    } finally {
      Remove-FixtureTree -Path $caseRoot
    }
  }
} catch {
  Write-Host "DESIGN-CHECK-REGRESSION: FAIL [unexpected] $($_.Exception.Message)"
  $failures += 1
} finally {
  Remove-FixtureTree -Path $fixtureRoot
  $finalSnapshot = Get-CallerSnapshot
  if ($finalSnapshot -ne $baselineSnapshot) {
    Write-Host "DESIGN-CHECK-REGRESSION: FAIL [clean-restoration] caller tracked state changed"
    $failures += 1
  } else {
    Write-Host "DESIGN-CHECK-REGRESSION: PASS [clean-restoration] caller tracked state unchanged"
  }
}

if ($rejectCount -ne 15 -or $acceptCount -ne 10) {
  Write-Host "DESIGN-CHECK-REGRESSION: FAIL [final-verdict-counts] expected 15 reject and 10 accept; got $rejectCount reject and $acceptCount accept"
  $failures += 1
}

if ($failures -gt 0) {
  Write-Host "DESIGN-CHECK-REGRESSION: $failures failures"
  exit 1
}

Write-Host "DESIGN-CHECK-REGRESSION: PASS [final-verdict-counts] (15 reject, 10 accept, production classifier, isolated Git fixtures)"
exit 0
