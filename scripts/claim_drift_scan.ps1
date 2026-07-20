#!/usr/bin/env pwsh

[CmdletBinding()]
param(
  [switch]$Strict,
  [string]$PolicyPath = "docs/internal/CLAIM_DRIFT_POLICY.json",
  [string[]]$Path = @("README.md", "artifact", "docs")
)

$ErrorActionPreference = "Continue"

if (-not (Test-Path $PolicyPath)) {
  Write-Host "CLAIM-DRIFT: policy not found: $PolicyPath"
  exit 1
}

$policy = Get-Content -Raw -Path $PolicyPath | ConvertFrom-Json
$currentFactSurfacePathRegex = [string]$policy.currentFactSurfacePathRegex
foreach ($term in @($policy.terms)) {
  $scope = [string]$term.scope
  if ([string]::IsNullOrWhiteSpace($scope)) {
    continue
  }
  if ($scope -ne "current-fact-surface") {
    Write-Host "CLAIM-DRIFT: unknown term scope '$scope' for $($term.id)"
    exit 1
  }
  if ([string]::IsNullOrWhiteSpace($currentFactSurfacePathRegex)) {
    Write-Host "CLAIM-DRIFT: current-fact-surface scope requires currentFactSurfacePathRegex"
    exit 1
  }
}
foreach ($attribution in @($policy.requiredAttributions)) {
  foreach ($field in @("id", "pathRegex", "claimPattern", "requiredPattern", "status")) {
    if ([string]::IsNullOrWhiteSpace([string]$attribution.$field)) {
      Write-Host "CLAIM-DRIFT: required attribution is missing '$field'"
      exit 1
    }
  }
  try {
    $null = [regex]::new([string]$attribution.pathRegex)
    $null = [regex]::new([string]$attribution.claimPattern)
    $null = [regex]::new([string]$attribution.requiredPattern)
  } catch {
    Write-Host "CLAIM-DRIFT: invalid required-attribution regex for $($attribution.id): $($_.Exception.Message)"
    exit 1
  }
}
$roots = @($Path | Where-Object { Test-Path $_ })

if ($roots.Count -eq 0) {
  Write-Host "CLAIM-DRIFT: no scan roots exist"
  exit 0
}

$failures = 0
$hits = 0
$repositoryRoot = [System.IO.Path]::GetFullPath((Get-Location).Path)
$pathComparison = [System.StringComparison]::Ordinal
if ($env:OS -eq "Windows_NT") {
  $pathComparison = [System.StringComparison]::OrdinalIgnoreCase
}

function Get-RipgrepJsonText {
  param($Value)

  if ($null -ne $Value.text) {
    return [string]$Value.text
  }
  if ($null -ne $Value.bytes) {
    return [System.Text.Encoding]::UTF8.GetString(
      [System.Convert]::FromBase64String([string]$Value.bytes)
    )
  }
  return ""
}

function ConvertTo-PolicyPath {
  param([string]$RipgrepPath)

  try {
    if ([System.IO.Path]::IsPathRooted($RipgrepPath)) {
      $fullPath = [System.IO.Path]::GetFullPath($RipgrepPath)
    } else {
      $fullPath = [System.IO.Path]::GetFullPath(
        [System.IO.Path]::Combine($repositoryRoot, $RipgrepPath)
      )
    }

    $rootWithSeparator = $repositoryRoot.TrimEnd(
      [System.IO.Path]::DirectorySeparatorChar,
      [System.IO.Path]::AltDirectorySeparatorChar
    ) + [System.IO.Path]::DirectorySeparatorChar
    if ($fullPath.StartsWith($rootWithSeparator, $pathComparison)) {
      return ($fullPath.Substring($rootWithSeparator.Length) -replace "\\", "/")
    }
  } catch {
    # Preserve a usable policy/display path even for an unusual rg path.
  }

  return ($RipgrepPath -replace "\\", "/")
}

function Get-ScanFiles {
  $files = @()
  foreach ($root in $roots) {
    $item = Get-Item -LiteralPath $root -ErrorAction SilentlyContinue
    if ($null -eq $item) {
      continue
    }
    if ($item.PSIsContainer) {
      $files += @(Get-ChildItem -LiteralPath $item.FullName -Recurse -File)
    } else {
      $files += $item
    }
  }
  return @($files | Sort-Object FullName -Unique)
}

function Get-MatchLineNumber {
  param(
    [string]$Content,
    [int]$Index
  )

  if ($Index -le 0) {
    return 1
  }
  return 1 + ([regex]::Matches($Content.Substring(0, $Index), "`n")).Count
}

foreach ($term in $policy.terms) {
  $pattern = [string]$term.pattern
  $rgArguments = @("--json", "--pcre2")
  if ($term.multiline -eq $true) {
    $rgArguments += "--multiline"
  }
  $rgArguments += @("--", $pattern)
  $rgArguments += @($roots)
  $matches = @(& rg @rgArguments 2>$null)
  $code = $LASTEXITCODE
  if ($code -gt 1) {
    Write-Host "CLAIM-DRIFT: rg failed for $($term.id)"
    exit $code
  }

  foreach ($jsonLine in $matches) {
    try {
      $record = $jsonLine | ConvertFrom-Json -ErrorAction Stop
    } catch {
      Write-Host "CLAIM-DRIFT: invalid rg JSON for $($term.id)"
      exit 1
    }
    if ($record.type -ne "match") {
      continue
    }

    $file = Get-RipgrepJsonText $record.data.path
    $fileNorm = ConvertTo-PolicyPath $file
    $lineNo = [string]$record.data.line_number
    $line = Get-RipgrepJsonText $record.data.lines
    $policyLine = $line.TrimEnd([char[]]"`r`n")
    $hits += 1

    $allowed = $false
    if ([string]$term.scope -eq "current-fact-surface" -and
        $fileNorm -notmatch $currentFactSurfacePathRegex) {
      $allowed = $true
    }
    if ($term.allowedPathRegex -and $fileNorm -match [string]$term.allowedPathRegex) {
      $allowed = $true
    }
    if ($term.allowedLineRegex -and $policyLine -match [string]$term.allowedLineRegex) {
      $allowed = $true
    }
    if (
      $term.allowedPathLinePathRegex -and
      $term.allowedPathLineRegex -and
      $fileNorm -match [string]$term.allowedPathLinePathRegex -and
      $policyLine -match [string]$term.allowedPathLineRegex
    ) {
      $allowed = $true
    }
    if ($term.allowedPathLinePairs) {
      foreach ($pair in @($term.allowedPathLinePairs)) {
        if (
          $pair.pathRegex -and
          $pair.lineRegex -and
          $fileNorm -match [string]$pair.pathRegex -and
          $policyLine -match [string]$pair.lineRegex
        ) {
          $allowed = $true
          break
        }
      }
    }

    $label = "review"
    if ($allowed) {
      $label = "allowed"
    }

    if ($Strict -and ($term.strict -eq $true) -and -not $allowed) {
      $label = "fail"
      $failures += 1
    }

    Write-Host ("CLAIM-DRIFT[{0}][{1}][{2}] {3}:{4}: {5}" -f $term.id, $term.status, $label, $file, $lineNo, $line.Trim())
  }
}

foreach ($attribution in @($policy.requiredAttributions)) {
  foreach ($fileItem in @(Get-ScanFiles)) {
    $fileNorm = ConvertTo-PolicyPath $fileItem.FullName
    if ($fileNorm -notmatch [string]$attribution.pathRegex) {
      continue
    }

    $content = Get-Content -Raw -LiteralPath $fileItem.FullName
    $claimMatch = [regex]::Match($content, [string]$attribution.claimPattern)
    if (-not $claimMatch.Success) {
      continue
    }

    $hits += 1
    $hasRequiredAttribution = [regex]::IsMatch(
      $content,
      [string]$attribution.requiredPattern
    )
    $label = if ($hasRequiredAttribution) { "allowed" } else { "review" }
    if ($Strict -and ($attribution.strict -eq $true) -and -not $hasRequiredAttribution) {
      $label = "fail"
      $failures += 1
    }
    $lineNo = Get-MatchLineNumber -Content $content -Index $claimMatch.Index
    $summary = if ($hasRequiredAttribution) {
      "strong claim has its required theorem identity"
    } else {
      "strong claim is missing required theorem identity"
    }
    Write-Host ("CLAIM-DRIFT[{0}][{1}][{2}] {3}:{4}: {5}" -f `
        $attribution.id, $attribution.status, $label, $fileNorm, $lineNo, $summary)
  }
}

if ($hits -eq 0) {
  Write-Host "CLAIM-DRIFT: no sensitive terms found"
}

if ($failures -gt 0) {
  Write-Host "CLAIM-DRIFT: strict mode found $failures unapproved sensitive matches"
  exit 1
}

Write-Host "CLAIM-DRIFT: scan complete ($hits hits, $failures strict failures)"
exit 0
