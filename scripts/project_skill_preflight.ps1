#!/usr/bin/env pwsh

[CmdletBinding()]
param(
  [Parameter(Mandatory = $true)]
  [string]$GovernanceRef,

  [Parameter(Mandatory = $true)]
  [string]$RequiredSkills,

  [AllowEmptyString()]
  [string]$RuntimeProjectSkills = "",

  [string]$CheckoutRef = "HEAD",
  [string]$RepositoryRoot
)

$ErrorActionPreference = "Stop"

function Stop-Preflight([string]$Message) {
  Write-Host "SKILL-PREFLIGHT: ERROR $Message"
  exit 2
}

function Invoke-Git([string[]]$Arguments) {
  $output = @(& git -C $script:RepositoryRoot @Arguments 2>&1)
  if ($LASTEXITCODE -ne 0) {
    throw "git $($Arguments -join ' ') failed:`n$($output -join [Environment]::NewLine)"
  }
  return $output
}

function Parse-SkillList([string]$Value) {
  if ([string]::IsNullOrWhiteSpace($Value)) { return @() }
  return @(
    $Value -split "[,;\s]+" |
      ForEach-Object { $_.Trim().TrimStart('$') } |
      Where-Object { $_ } |
      Sort-Object -Unique
  )
}

function Get-RefSkillInventory([string]$Commit) {
  $paths = @(Invoke-Git @("ls-tree", "-r", "--name-only", $Commit, "--", ".agents/skills"))
  return @(
    $paths |
      ForEach-Object {
        if ($_ -match '^\.agents/skills/([^/]+)/SKILL\.md$') { $Matches[1] }
      } |
      Where-Object { $_ } |
      Sort-Object -Unique
  )
}

function Get-WorkingSkillInventory([string]$Root) {
  $skillsRoot = Join-Path $Root ".agents\skills"
  if (-not (Test-Path -LiteralPath $skillsRoot -PathType Container)) { return @() }
  return @(
    Get-ChildItem -LiteralPath $skillsRoot -Directory |
      Where-Object { Test-Path -LiteralPath (Join-Path $_.FullName "SKILL.md") -PathType Leaf } |
      ForEach-Object { $_.Name } |
      Sort-Object -Unique
  )
}

function Get-FrontmatterName([string[]]$Lines) {
  foreach ($line in $Lines) {
    if ($line -match '^name:\s*["'']?([^"'']+?)["'']?\s*$') {
      return $Matches[1].Trim()
    }
  }
  return $null
}

try {
  if (-not $RepositoryRoot) {
    $RepositoryRoot = (& git rev-parse --show-toplevel 2>&1).Trim()
    if ($LASTEXITCODE -ne 0) { Stop-Preflight "not inside a Git repository" }
  }
  $RepositoryRoot = (Resolve-Path -LiteralPath $RepositoryRoot).Path

  $governanceSha = (@(Invoke-Git @("rev-parse", "${GovernanceRef}^{commit}")))[0].Trim()
  $checkoutSha = (@(Invoke-Git @("rev-parse", "${CheckoutRef}^{commit}")))[0].Trim()
  $expectedSkills = @(Get-RefSkillInventory $governanceSha)
  $checkoutSkills = @(Get-RefSkillInventory $checkoutSha)
  $workingSkills = @(Get-WorkingSkillInventory $RepositoryRoot)
  $runtimeSkills = @(Parse-SkillList $RuntimeProjectSkills)
  $required = @(Parse-SkillList $RequiredSkills)

  if ($expectedSkills.Count -eq 0) {
    Stop-Preflight "governance ref $governanceSha defines no repo-local skills"
  }
  if ($required.Count -eq 0) {
    Stop-Preflight "at least one applicable skill must be required explicitly"
  }

  & git -C $RepositoryRoot merge-base --is-ancestor $governanceSha $checkoutSha 2>$null
  $governanceInCheckout = $LASTEXITCODE -eq 0

  $undefinedRequired = @($required | Where-Object { $_ -notin $expectedSkills })
  $missingCheckout = @($expectedSkills | Where-Object { $_ -notin $checkoutSkills })
  $missingWorking = @($expectedSkills | Where-Object { $_ -notin $workingSkills })
  $missingRequiredRuntime = @($required | Where-Object { $_ -notin $runtimeSkills })
  $staleCheckout = @()
  $staleWorking = @()
  $frontmatterMismatch = @()

  foreach ($skill in $expectedSkills) {
    $expectedSkillPath = ".agents/skills/$skill"
    $expectedTree = (@(Invoke-Git @("rev-parse", "${governanceSha}:$expectedSkillPath")))[0].Trim()

    if ($skill -in $checkoutSkills) {
      $checkoutTree = (@(Invoke-Git @("rev-parse", "${checkoutSha}:$expectedSkillPath")))[0].Trim()
      if ($checkoutTree -ne $expectedTree) { $staleCheckout += $skill }
    }

    $expectedSkillFile = "$expectedSkillPath/SKILL.md"
    $expectedLines = @(Invoke-Git @("show", "${governanceSha}:$expectedSkillFile"))
    $expectedName = Get-FrontmatterName $expectedLines
    if ($expectedName -ne $skill) {
      $frontmatterMismatch += "$skill(expected:$expectedName)"
    }

    $workingSkillFile = Join-Path $RepositoryRoot ($expectedSkillFile -replace '/', '\')
    if (Test-Path -LiteralPath $workingSkillFile -PathType Leaf) {
      $workingName = Get-FrontmatterName @(Get-Content -LiteralPath $workingSkillFile)
      if ($workingName -ne $skill) {
        $frontmatterMismatch += "$skill(working:$workingName)"
      }

      & git -C $RepositoryRoot diff --quiet $governanceSha -- $expectedSkillPath
      if ($LASTEXITCODE -ne 0) { $staleWorking += $skill }
    }
  }

  $requiredUnavailable = @(
    $required |
      Where-Object {
        $_ -in $undefinedRequired -or
        $_ -in $missingCheckout -or
        $_ -in $missingWorking -or
        $_ -in $missingRequiredRuntime -or
        $_ -in $staleCheckout -or
        $_ -in $staleWorking
      } |
      Sort-Object -Unique
  )

  Write-Host "SKILL-PREFLIGHT: governance=$governanceSha"
  Write-Host "SKILL-PREFLIGHT: checkout=$checkoutSha"
  Write-Host "SKILL-PREFLIGHT: expected=$($expectedSkills -join ',')"
  Write-Host "SKILL-PREFLIGHT: checkout_skills=$($checkoutSkills -join ',')"
  Write-Host "SKILL-PREFLIGHT: working_skills=$($workingSkills -join ',')"
  Write-Host "SKILL-PREFLIGHT: runtime_skills=$($runtimeSkills -join ',')"
  Write-Host "SKILL-PREFLIGHT: required=$($required -join ',')"

  $failures = @()
  if (-not $governanceInCheckout) { $failures += "governance_not_in_checkout_ancestry" }
  if ($runtimeSkills.Count -eq 0) { $failures += "runtime_catalog_omitted" }
  if ($undefinedRequired.Count) { $failures += "required_not_defined=$($undefinedRequired -join ',')" }
  if ($missingCheckout.Count) { $failures += "missing_from_checkout=$($missingCheckout -join ',')" }
  if ($missingWorking.Count) { $failures += "missing_from_working_tree=$($missingWorking -join ',')" }
  if ($missingRequiredRuntime.Count) { $failures += "missing_required_from_runtime=$($missingRequiredRuntime -join ',')" }
  if ($staleCheckout.Count) { $failures += "stale_in_checkout=$($staleCheckout -join ',')" }
  if ($staleWorking.Count) { $failures += "stale_in_working_tree=$($staleWorking -join ',')" }
  if ($frontmatterMismatch.Count) { $failures += "frontmatter_mismatch=$($frontmatterMismatch -join ',')" }
  if ($requiredUnavailable.Count) { $failures += "required_unavailable=$($requiredUnavailable -join ',')" }

  if ($failures.Count) {
    foreach ($failure in $failures) { Write-Host "SKILL-PREFLIGHT: FAIL $failure" }
    Write-Host "SKILL-PREFLIGHT: ACTION STOP; notify the user and restart from a governance-containing checkout whose runtime exposes every explicitly required RMQ role skill. Do not substitute another skill."
    exit 2
  }

  Write-Host "SKILL-PREFLIGHT: PASS"
  exit 0
} catch {
  Stop-Preflight $_.Exception.Message
}
