#!/usr/bin/env pwsh

[CmdletBinding()]
param(
  [switch]$Strict,
  [string]$PolicyPath = "docs/internal/CLAIM_DRIFT_POLICY.json",
  [string]$DocumentRolesPath = "docs/internal/PUBLICATION_DOCUMENT_ROLES.json",
  [string[]]$Path = @("README.md", "artifact", "docs")
)

$ErrorActionPreference = "Continue"

if (-not (Test-Path $PolicyPath)) {
  Write-Host "CLAIM-DRIFT: policy not found: $PolicyPath"
  exit 1
}

if (-not (Test-Path $DocumentRolesPath)) {
  Write-Host "CLAIM-DRIFT: document-role manifest not found: $DocumentRolesPath"
  exit 1
}

$policy = Get-Content -Raw -Path $PolicyPath | ConvertFrom-Json
$documentRoleManifest = Get-Content -Raw -Path $DocumentRolesPath |
  ConvertFrom-Json
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

function Get-DocumentRole {
  param([string]$PolicyPathValue)

  foreach ($roleDefinition in @($documentRoleManifest.roles)) {
    foreach ($document in @($roleDefinition.documents)) {
      $documentPath = ([string]$document.path) -replace "\\", "/"
      if ($documentPath -eq $PolicyPathValue) {
        return [string]$roleDefinition.role
      }
    }
    foreach ($pathRegex in @($roleDefinition.pathRegexes)) {
      if ($pathRegex -and $PolicyPathValue -match [string]$pathRegex) {
        return [string]$roleDefinition.role
      }
    }
  }
  return ""
}

function Test-ExactFrozenSnapshotLine {
  param(
    [string]$PolicyPathValue,
    [string]$PolicyLineValue
  )

  $frozenRole = @($documentRoleManifest.roles |
      Where-Object { $_.role -eq "exact-frozen-snapshot" })
  foreach ($roleDefinition in $frozenRole) {
    foreach ($document in @($roleDefinition.documents)) {
      $documentPath = ([string]$document.path) -replace "\\", "/"
      if ($documentPath -ne $PolicyPathValue) { continue }
      foreach ($exactLine in @($document.exactLines)) {
        if ($PolicyLineValue -ceq [string]$exactLine) {
          return $true
        }
      }
    }
  }
  return $false
}

foreach ($term in $policy.terms) {
  $pattern = [string]$term.pattern
  $matches = @(& rg --json --pcre2 -- $pattern @roots 2>$null)
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
    $documentRole = Get-DocumentRole $fileNorm
    $hits += 1

    $allowed = $false
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
    if ($term.allowedDocumentRoles -and
        @($term.allowedDocumentRoles) -contains $documentRole) {
      $allowed = $true
    }
    if ($term.allowExactFrozenSnapshot -eq $true -and
        (Test-ExactFrozenSnapshotLine $fileNorm $policyLine)) {
      $allowed = $true
    }

    $label = "review"
    if ($allowed) {
      $label = "allowed"
    }

    $strictApplies = ($term.strict -eq $true)
    if ($term.strictDocumentRoles) {
      $strictApplies = $strictApplies -and
        (@($term.strictDocumentRoles) -contains $documentRole)
    }
    if ($Strict -and $strictApplies -and -not $allowed) {
      $label = "fail"
      $failures += 1
    }

    Write-Host ("CLAIM-DRIFT[{0}][{1}][{2}] {3}:{4}: {5}" -f $term.id, $term.status, $label, $file, $lineNo, $line.Trim())
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
