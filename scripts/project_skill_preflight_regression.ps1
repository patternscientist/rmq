#!/usr/bin/env pwsh

$ErrorActionPreference = "Stop"

function Fail([string]$Message) {
  Write-Host "SKILL-PREFLIGHT-REGRESSION: FAIL $Message"
  exit 1
}

function Write-Skill([string]$Root, [string]$Name, [string]$Description) {
  $dir = Join-Path $Root ".agents\skills\$Name"
  New-Item -ItemType Directory -Force -Path $dir | Out-Null
  @(
    "---"
    "name: $Name"
    "description: $Description"
    "---"
    ""
    "# $Name"
  ) | Set-Content -LiteralPath (Join-Path $dir "SKILL.md") -Encoding utf8
}

function Invoke-Case(
  [string]$Name,
  [int]$ExpectedExit,
  [string]$GovernanceRef,
  [string]$RequiredSkills,
  [string]$RuntimeSkills,
  [string[]]$RequiredOutput = @()
) {
  $arguments = @(
    "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", $preflight,
    "-RepositoryRoot", $tempRoot,
    "-GovernanceRef", $GovernanceRef,
    "-RequiredSkills", $RequiredSkills
  )
  if ($RuntimeSkills) { $arguments += @("-RuntimeProjectSkills", $RuntimeSkills) }
  $output = @(& powershell @arguments 2>&1)
  $exitCode = $LASTEXITCODE
  if ($exitCode -ne $ExpectedExit) {
    Fail "$Name expected exit $ExpectedExit, got $exitCode`n$($output -join [Environment]::NewLine)"
  }
  foreach ($pattern in $RequiredOutput) {
    if (-not ($output -match $pattern)) {
      Fail "$Name did not emit '$pattern'`n$($output -join [Environment]::NewLine)"
    }
  }
  Write-Host "SKILL-PREFLIGHT-REGRESSION: PASS $Name"
}

$preflight = Join-Path $PSScriptRoot "project_skill_preflight.ps1"
if (-not (Test-Path -LiteralPath $preflight -PathType Leaf)) {
  Fail "production preflight script is missing"
}

$tempRoot = Join-Path ([IO.Path]::GetTempPath()) ("rmq-skill-preflight-" + [guid]::NewGuid().ToString("N"))
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
  & git -C $tempRoot config user.email "rmq-skill-preflight@example.invalid"
  & git -C $tempRoot config user.name "RMQ Skill Preflight"

  Write-Skill $tempRoot "rmq-proof-sprint" "Proof worker fixture."
  & git -C $tempRoot add .agents/skills
  & git -C $tempRoot -c commit.gpgSign=false commit --quiet -m "stale skill frontier"
  if ($LASTEXITCODE -ne 0) { Fail "could not commit stale fixture" }
  $staleRef = (& git -C $tempRoot rev-parse HEAD).Trim()

  Write-Skill $tempRoot "rmq-coordinator" "Coordinator fixture."
  Write-Skill $tempRoot "rmq-audit" "Audit fixture."
  & git -C $tempRoot add .agents/skills
  & git -C $tempRoot -c commit.gpgSign=false commit --quiet -m "current skill frontier"
  if ($LASTEXITCODE -ne 0) { Fail "could not commit current fixture" }
  $currentRef = (& git -C $tempRoot rev-parse HEAD).Trim()

  & git -C $tempRoot checkout --quiet $staleRef
  Invoke-Case "stale-checkout-and-runtime" 2 $currentRef "rmq-coordinator" `
    "rmq-proof-sprint" @(
      "missing_from_checkout=rmq-audit,rmq-coordinator",
      "missing_from_runtime=rmq-audit,rmq-coordinator",
      "required_unavailable=rmq-coordinator",
      "ACTION STOP"
    )

  & git -C $tempRoot checkout --quiet $currentRef
  Invoke-Case "current-checkout-stale-runtime" 2 $currentRef "rmq-coordinator" `
    "rmq-proof-sprint" @("missing_from_runtime=rmq-audit,rmq-coordinator", "ACTION STOP")

  Invoke-Case "complete-runtime-catalog" 0 $currentRef "rmq-coordinator" `
    "rmq-audit,rmq-coordinator,rmq-proof-sprint" @("SKILL-PREFLIGHT: PASS")

  Invoke-Case "extra-nonproject-skills-ignored" 0 $currentRef "rmq-coordinator" `
    "openai-docs,rmq-audit,rmq-coordinator,rmq-proof-sprint" @("SKILL-PREFLIGHT: PASS")

  Invoke-Case "omitted-runtime-catalog" 2 $currentRef "rmq-coordinator" "" `
    @("runtime_catalog_omitted", "ACTION STOP")

  Invoke-Case "undefined-required-skill" 2 $currentRef "rmq-nonexistent" `
    "rmq-audit,rmq-coordinator,rmq-proof-sprint" @("required_not_defined=rmq-nonexistent")

  $coordinatorSkill = Join-Path $tempRoot ".agents\skills\rmq-coordinator\SKILL.md"
  (Get-Content -LiteralPath $coordinatorSkill) -replace '^name: rmq-coordinator$', 'name: wrong-name' |
    Set-Content -LiteralPath $coordinatorSkill -Encoding utf8
  Invoke-Case "frontmatter-name-mismatch" 2 $currentRef "rmq-coordinator" `
    "rmq-audit,rmq-coordinator,rmq-proof-sprint" @("frontmatter_mismatch=rmq-coordinator")

  Write-Host "SKILL-PREFLIGHT-REGRESSION: PASS all cases"
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
