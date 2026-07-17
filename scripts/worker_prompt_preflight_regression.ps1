#!/usr/bin/env pwsh

$ErrorActionPreference = "Stop"

function Fail([string]$Message) {
  Write-Host "WORKER-PROMPT-REGRESSION: FAIL $Message"
  exit 1
}

$powerShellExecutable = (Get-Process -Id $PID).Path
if (-not $powerShellExecutable) {
  Fail "could not resolve the current PowerShell executable"
}

function Write-Prompt(
  [string]$Path,
  [string]$FirstLine,
  [string]$Governance,
  [string]$Base,
  [string]$Branch,
  [string[]]$Extra = @()
) {
  @(
    $FirstLine
    "Use `$rmq-proof-sprint before starting."
    "Workflow-governance ref: $Governance"
    "Exact base: $Base"
    "Create branch exactly $Branch"
  ) + $Extra | Set-Content -LiteralPath $Path -Encoding utf8
}

function Invoke-Case(
  [string]$Name,
  [int]$ExpectedExit,
  [string]$PromptPath,
  [string]$Governance,
  [string]$Base,
  [string]$Status,
  [string]$Feedback,
  [string[]]$RequiredOutput = @()
) {
  $arguments = @(
    "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", $preflight,
    "-RepositoryRoot", $tempRoot,
    "-PromptPath", $PromptPath,
    "-GovernanceRef", $Governance,
    "-WorkerBase", $Base,
    "-WorkerHandle", "E1-01R1",
    "-RequestedTitle", "(E1-01R1) Repair the machine",
    "-RequiredSkill", "rmq-proof-sprint",
    "-PromptStatus", $Status,
    "-FailureModeFeedbackStatus", $Feedback,
    "-TaskMode", "WRITE",
    "-WorkerBranch", "codex/e1-repair"
  )
  $output = @(& $script:powerShellExecutable @arguments 2>&1)
  $exitCode = $LASTEXITCODE
  if ($exitCode -ne $ExpectedExit) {
    Fail "$Name expected exit $ExpectedExit, got $exitCode`n$($output -join [Environment]::NewLine)"
  }
  foreach ($pattern in $RequiredOutput) {
    if (-not ($output -match $pattern)) {
      Fail "$Name did not emit '$pattern'`n$($output -join [Environment]::NewLine)"
    }
  }
  Write-Host "WORKER-PROMPT-REGRESSION: PASS $Name"
}

$preflight = Join-Path $PSScriptRoot "worker_prompt_preflight.ps1"
if (-not (Test-Path -LiteralPath $preflight -PathType Leaf)) {
  Fail "production worker prompt preflight is missing"
}

$tempRoot = Join-Path ([IO.Path]::GetTempPath()) ("rmq-worker-prompt-" + [guid]::NewGuid().ToString("N"))
New-Item -ItemType Directory -Path $tempRoot | Out-Null
$oldGitConfigGlobal = $env:GIT_CONFIG_GLOBAL
$oldGitConfigCount = $env:GIT_CONFIG_COUNT
$oldGitConfigKey0 = $env:GIT_CONFIG_KEY_0
$oldGitConfigValue0 = $env:GIT_CONFIG_VALUE_0
$tempExcludesFile = Join-Path $tempRoot ".gitignore-global"
New-Item -ItemType File -Path $tempExcludesFile | Out-Null
$env:GIT_CONFIG_GLOBAL = "NUL"
$env:GIT_CONFIG_COUNT = "1"
$env:GIT_CONFIG_KEY_0 = "core.excludesFile"
$env:GIT_CONFIG_VALUE_0 = $tempExcludesFile

try {
  & git -C $tempRoot init --quiet
  if ($LASTEXITCODE -ne 0) { Fail "could not initialize fixture repository" }
  & git -C $tempRoot config user.email "rmq-worker-prompt@example.invalid"
  & git -C $tempRoot config user.name "RMQ Worker Prompt"

  "root" | Set-Content -LiteralPath (Join-Path $tempRoot "root.txt") -Encoding utf8
  & git -C $tempRoot add root.txt
  & git -C $tempRoot -c commit.gpgSign=false commit --quiet -m "fixture root"
  $rootRef = (& git -C $tempRoot rev-parse HEAD).Trim()

  & git -C $tempRoot switch --quiet -c stale-base
  "stale" | Set-Content -LiteralPath (Join-Path $tempRoot "stale.txt") -Encoding utf8
  & git -C $tempRoot add stale.txt
  & git -C $tempRoot -c commit.gpgSign=false commit --quiet -m "stale worker base"
  $staleRef = (& git -C $tempRoot rev-parse HEAD).Trim()

  & git -C $tempRoot switch --quiet -c governance $rootRef
  "policy" | Set-Content -LiteralPath (Join-Path $tempRoot "policy.txt") -Encoding utf8
  & git -C $tempRoot add policy.txt
  & git -C $tempRoot -c commit.gpgSign=false commit --quiet -m "governance"
  $governanceRef = (& git -C $tempRoot rev-parse HEAD).Trim()

  "worker" | Set-Content -LiteralPath (Join-Path $tempRoot "worker.txt") -Encoding utf8
  & git -C $tempRoot add worker.txt
  & git -C $tempRoot -c commit.gpgSign=false commit --quiet -m "governed worker base"
  $workerBase = (& git -C $tempRoot rev-parse HEAD).Trim()

  $validPrompt = Join-Path $tempRoot "valid-prompt.txt"
  Write-Prompt $validPrompt "Make the title of this chat exactly: (E1-01R1) Repair the machine" `
    $governanceRef $workerBase "codex/e1-repair"
  Invoke-Case "ready-governed" 0 $validPrompt $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("WORKER-PROMPT-PREFLIGHT: PASS")

  $metadataTitle = Join-Path $tempRoot "metadata-title.txt"
  Write-Prompt $metadataTitle "Title: (E1-01R1) Repair the machine" `
    $governanceRef $workerBase "codex/e1-repair"
  Invoke-Case "title-metadata-only" 2 $metadataTitle $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("first line must be exactly")

  $stalePrompt = Join-Path $tempRoot "stale-base.txt"
  Write-Prompt $stalePrompt "Make the title of this chat exactly: (E1-01R1) Repair the machine" `
    $governanceRef $staleRef "codex/e1-repair"
  Invoke-Case "stale-worker-base" 2 $stalePrompt $governanceRef $staleRef `
    "READY_TO_SEND" "COMPLETE" @("does not contain governance")

  Invoke-Case "ready-feedback-pending" 2 $validPrompt $governanceRef $workerBase `
    "READY_TO_SEND" "PENDING" @("READY_TO_SEND requires failure-mode feedback")

  Invoke-Case "draft-feedback-pending" 0 $validPrompt $governanceRef $workerBase `
    "DRAFT_DO_NOT_SEND" "PENDING" @("status=DRAFT_DO_NOT_SEND", "PASS")

  $placeholderPrompt = Join-Path $tempRoot "placeholder.txt"
  Write-Prompt $placeholderPrompt "Make the title of this chat exactly: (E1-01R1) Repair the machine" `
    $governanceRef $workerBase "codex/e1-repair" @("Write scope: [PATHS]")
  Invoke-Case "template-placeholder" 2 $placeholderPrompt $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("template placeholder")

  Write-Host "WORKER-PROMPT-REGRESSION: PASS all cases"
  exit 0
} finally {
  if ($null -eq $oldGitConfigGlobal) {
    Remove-Item Env:GIT_CONFIG_GLOBAL -ErrorAction SilentlyContinue
  } else {
    $env:GIT_CONFIG_GLOBAL = $oldGitConfigGlobal
  }
  foreach ($entry in @(
    @{ Name = "GIT_CONFIG_COUNT"; Value = $oldGitConfigCount },
    @{ Name = "GIT_CONFIG_KEY_0"; Value = $oldGitConfigKey0 },
    @{ Name = "GIT_CONFIG_VALUE_0"; Value = $oldGitConfigValue0 }
  )) {
    if ($null -eq $entry.Value) {
      Remove-Item "Env:$($entry.Name)" -ErrorAction SilentlyContinue
    } else {
      Set-Item "Env:$($entry.Name)" $entry.Value
    }
  }
  Remove-Item -LiteralPath $tempRoot -Recurse -Force -ErrorAction SilentlyContinue
}
