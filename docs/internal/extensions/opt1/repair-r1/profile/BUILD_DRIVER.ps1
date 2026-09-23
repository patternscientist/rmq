#!/usr/bin/env pwsh
# Library only: dot-sourcing defines the production profile API; it never builds.
# Trusted order: versioned manifest -> this builder -> actual build receipt ->
# externally pinned certificate runner. The live input never supplies a baseline.

function Get-OPT1ProfileHash([byte[]]$Bytes) {
  $digest = [Security.Cryptography.SHA256]::Create()
  try { return ([BitConverter]::ToString($digest.ComputeHash($Bytes))).Replace('-', '').ToLowerInvariant() }
  finally { $digest.Dispose() }
}

function Get-OPT1ProfileCanonicalBytes([byte[]]$Bytes, [string]$Label) {
  $encoding = [Text.UTF8Encoding]::new($false, $true)
  try { $text = $encoding.GetString($Bytes) }
  catch { throw "OPT1-PROFILE: invalid strict UTF-8: $Label" }
  if ($text.StartsWith([string][char]0xFEFF, [StringComparison]::Ordinal) -or
      $text.Replace("`r`n", '').Contains("`r")) {
    throw "OPT1-PROFILE: BOM or bare CR outside serialization: $Label"
  }
  return ,$encoding.GetBytes($text.Replace("`r`n", "`n"))
}

function Write-OPT1ProfileJson([string]$Path, [object]$Value) {
  [void][IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName([IO.Path]::GetFullPath($Path)))
  [IO.File]::WriteAllText($Path, (($Value | ConvertTo-Json -Depth 20) + "`n"), [Text.UTF8Encoding]::new($false, $true))
}

function Read-OPT1ReplayProfile([string]$RepoRoot) {
  $path = Join-Path $RepoRoot 'docs/internal/extensions/opt1/repair-r1/profile/SOURCE_PROFILE.json'
  $bytes = [IO.File]::ReadAllBytes($path)
  $expected = 'b83ada3baa438d812da076b48422c0a92f88ce686cd48ef982f39de7701699c9'
  if ((Get-OPT1ProfileHash $bytes) -cne $expected) { throw 'OPT1-PROFILE: pinned source manifest bytes changed' }
  $manifest = [Text.UTF8Encoding]::new($false, $true).GetString($bytes) | ConvertFrom-Json
  if ($manifest.Version -cne 'opt1-r1-source-profile-v1' -or
      $manifest.SourceCommit -cne 'aecf4a580c591e8f694a3699e19e843198089194' -or
      @($manifest.Sources).Count -ne 263 -or @($manifest.RuntimeImports).Count -ne 261 -or
      @($manifest.ToolchainFiles).Count -ne 4823) { throw 'OPT1-PROFILE: manifest contract mismatch' }
  return $manifest
}

function Assert-OPT1ProfileSourceEntries([string]$RepoRoot, [object]$Manifest) {
  $snapshot = [ordered]@{}
  foreach ($entry in @($Manifest.Sources) + @($Manifest.Configuration)) {
    $path = Join-Path $RepoRoot $entry.Path
    if (-not [IO.File]::Exists($path)) { throw "OPT1-PROFILE: missing source/configuration: $($entry.Path)" }
    $raw = [IO.File]::ReadAllBytes($path)
    $canonical = Get-OPT1ProfileCanonicalBytes $raw $entry.Path
    if ($canonical.Length -ne $entry.CanonicalLength -or
        (Get-OPT1ProfileHash $canonical) -cne $entry.CanonicalSHA256) {
      throw "OPT1-PROFILE: source/configuration differs from versioned Git identity: $($entry.Path)"
    }
    $snapshot[$entry.Path] = Get-OPT1ProfileHash $raw
  }
  return $snapshot
}

function Assert-OPT1ProfileToolchain([string]$LeanPath, [object]$Manifest) {
  $leanFull = [IO.Path]::GetFullPath($LeanPath)
  $toolRoot = [IO.Path]::GetDirectoryName([IO.Path]::GetDirectoryName($leanFull))
  if ($leanFull.Replace('\', '/') -cne (Join-Path $toolRoot $Manifest.LeanRelativePath).Replace('\', '/')) {
    throw 'OPT1-PROFILE: wrong Lean executable/profile path'
  }
  $actualNames = @(foreach ($directory in $Manifest.ToolchainInventoryRoots) {
    $directoryPath = Join-Path $toolRoot $directory
    if (-not [IO.Directory]::Exists($directoryPath)) { throw "OPT1-PROFILE: missing toolchain inventory root $directory" }
    foreach ($file in [IO.Directory]::EnumerateFiles($directoryPath, '*', [IO.SearchOption]::AllDirectories)) {
      $file.Substring($toolRoot.Length + 1).Replace('\', '/')
    }
  })
  $expectedNames = @($Manifest.ToolchainFiles.Path)
  if ($actualNames.Count -ne $expectedNames.Count -or
      (@($actualNames | Sort-Object) -join "`n") -cne (@($expectedNames | Sort-Object) -join "`n")) {
    throw 'OPT1-PROFILE: changed complete executable/library inventory'
  }
  foreach ($entry in $Manifest.ToolchainFiles) {
    $path = Join-Path $toolRoot $entry.Path
    if (([IO.FileInfo]::new($path)).Length -ne $entry.Length -or
        (Get-FileHash -Algorithm SHA256 -LiteralPath $path).Hash.ToLowerInvariant() -cne $entry.SHA256) {
      throw "OPT1-PROFILE: toolchain executable/library bytes changed: $($entry.Path)"
    }
  }
  return $toolRoot
}

function Assert-OPT1ReplaySources([string]$RepoRoot, [string]$LeanPath) {
  $manifest = Read-OPT1ReplayProfile $RepoRoot
  $null = Assert-OPT1ProfileSourceEntries $RepoRoot $manifest
  $null = Assert-OPT1ProfileToolchain $LeanPath $manifest
  return $manifest
}

function Read-OPT1ReplayBuildReceipt([string]$RepoRoot, [string]$ExpectedReceiptSHA256) {
  if ($ExpectedReceiptSHA256 -cnotmatch '^[0-9a-f]{64}$') { throw 'OPT1-PROFILE: external build-receipt pin required' }
  $path = Join-Path $RepoRoot 'docs/internal/extensions/opt1/repair-r1/profile/BUILD_RECEIPT.json'
  $bytes = [IO.File]::ReadAllBytes($path)
  if ((Get-OPT1ProfileHash $bytes) -cne $ExpectedReceiptSHA256) { throw 'OPT1-PROFILE: pinned build receipt bytes changed' }
  $receipt = [Text.UTF8Encoding]::new($false, $true).GetString($bytes) | ConvertFrom-Json
  $manifestBytes = [IO.File]::ReadAllBytes((Join-Path $RepoRoot 'docs/internal/extensions/opt1/repair-r1/profile/SOURCE_PROFILE.json'))
  $builderBytes = Get-OPT1ProfileCanonicalBytes ([IO.File]::ReadAllBytes((Join-Path $RepoRoot 'scripts/packed_optimized_replay_profile.ps1'))) 'profile builder'
  if ($receipt.Version -cne 'opt1-r1-build-receipt-v1' -or $receipt.Completed -ne $true -or
      $receipt.SourceCommit -cne 'aecf4a580c591e8f694a3699e19e843198089194' -or
      $receipt.SourceProfileSHA256 -cne (Get-OPT1ProfileHash $manifestBytes) -or
      $receipt.BuilderCanonicalSHA256 -cne (Get-OPT1ProfileHash $builderBytes) -or
      $receipt.CanonicalBuildProfile -cne 'raw-git-lf-relative-lean-source' -or
      @($receipt.Modules).Count -ne 263 -or @($receipt.RuntimeImports).Count -ne 261) {
    throw 'OPT1-PROFILE: build/source/script/profile linkage mismatch'
  }
  return $receipt
}

function Assert-OPT1ProfileArtifacts([string]$ArtifactDirectory, [object]$Manifest, [object]$Receipt) {
  if ((@($Receipt.Modules.Module) -join "`n") -cne (@($Manifest.BuildOrder) -join "`n") -or
      (@($Receipt.RuntimeImports.Module) -join "`n") -cne (@($Manifest.RuntimeImports) -join "`n")) {
    throw 'OPT1-PROFILE: missing/duplicate/reordered build or runtime dependency'
  }
  $outputHashes = @{}
  foreach ($module in $Receipt.Modules) { $outputHashes[$module.Module] = $module.ArtifactSHA256 }
  foreach ($entry in $Receipt.Modules) {
    $source = @($Manifest.Sources | Where-Object { $_.Module -ceq $entry.Module })[0]
    $relative = $entry.Module.Replace('.', '/') + '.olean'
    $path = Join-Path $ArtifactDirectory $relative
    if ($entry.SourceBeforeSHA256 -cne $source.CanonicalSHA256 -or
        $entry.SourceAfterSHA256 -cne $source.CanonicalSHA256 -or
        $entry.Artifact -cne ('.lake/build/lib/lean/' + $relative) -or
        $entry.Result.ExitCode -ne 0 -or $entry.Result.TimedOut -or $entry.Result.OutputLimitExceeded -or
        $entry.Result.Ownership -cne 'kill-on-close-job' -or
        -not [IO.File]::Exists($path) -or
        (Get-FileHash -Algorithm SHA256 -LiteralPath $path).Hash.ToLowerInvariant() -cne $entry.ArtifactSHA256) {
      throw "OPT1-PROFILE: missing/changed/stale compiled artifact or receipt: $($entry.Module)"
    }
    $expectedDeps = @('Init') + @($source.Imports)
    if ((@($entry.Dependencies.Module) -join "`n") -cne ($expectedDeps -join "`n")) {
      throw "OPT1-PROFILE: omitted/changed direct dependency: $($entry.Module)"
    }
    foreach ($dependency in $entry.Dependencies) {
      $hash = if ($dependency.Module.StartsWith('RMQ.', [StringComparison]::Ordinal)) {
        $outputHashes[$dependency.Module]
      } else {
        $toolPath = 'lib/lean/' + $dependency.Module.Replace('.', '/') + '.olean'
        @($Manifest.ToolchainFiles | Where-Object { $_.Path -ceq $toolPath })[0].SHA256
      }
      if ($dependency.ArtifactSHA256 -cne $hash) { throw "OPT1-PROFILE: dependency artifact linkage changed: $($entry.Module)" }
    }
  }
  foreach ($runtime in $Receipt.RuntimeImports) {
    if ($runtime.Source -cne ($runtime.Module.Replace('.', '/') + '.lean') -or
        $runtime.Artifact -cne ('.lake/build/lib/lean/' + $runtime.Module.Replace('.', '/') + '.olean') -or
        $runtime.ArtifactSHA256 -cne $outputHashes[$runtime.Module]) {
      throw 'OPT1-PROFILE: runtime/build artifact identity mismatch'
    }
  }
}

function Assert-OPT1ReplayProfile([string]$RepoRoot, [string]$LeanPath, [string]$ExpectedReceiptSHA256) {
  $manifest = Assert-OPT1ReplaySources $RepoRoot $LeanPath
  $receipt = Read-OPT1ReplayBuildReceipt $RepoRoot $ExpectedReceiptSHA256
  Assert-OPT1ProfileArtifacts (Join-Path $RepoRoot '.lake/build/lib/lean') $manifest $receipt
  return [pscustomobject]@{
    SourceCommit=$manifest.SourceCommit; SourceProfileSHA256=$receipt.SourceProfileSHA256
    BuildReceiptSHA256=$ExpectedReceiptSHA256; RuntimeImports=@($receipt.RuntimeImports)
  }
}

function Install-OPT1ReplayArtifacts([string]$RepoRoot, [string]$LeanPath,
    [string]$ExpectedReceiptSHA256, [string]$ArtifactDirectory) {
  $manifest = Assert-OPT1ReplaySources $RepoRoot $LeanPath
  $receipt = Read-OPT1ReplayBuildReceipt $RepoRoot $ExpectedReceiptSHA256
  Assert-OPT1ProfileArtifacts $ArtifactDirectory $manifest $receipt
  foreach ($entry in $receipt.Modules) {
    $relative = $entry.Module.Replace('.', '/') + '.olean'
    $source = [IO.Path]::GetFullPath((Join-Path $ArtifactDirectory $relative))
    $target = [IO.Path]::GetFullPath((Join-Path $RepoRoot $entry.Artifact))
    if ($source -ceq $target) { throw 'OPT1-PROFILE: installation requires a distinct private source cache' }
    [void][IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($target))
    # Copy creates independent bytes. There are no shared mutable links.
    [IO.File]::Copy($source, $target, $true)
    if ((Get-FileHash -Algorithm SHA256 -LiteralPath $target).Hash.ToLowerInvariant() -cne $entry.ArtifactSHA256) {
      throw "OPT1-PROFILE: copied artifact changed: $($entry.Module)"
    }
  }
  return Assert-OPT1ReplayProfile $RepoRoot $LeanPath $ExpectedReceiptSHA256
}

function Build-OPT1ReplayProfile([string]$RepoRoot, [string]$LeanPath,
    [string]$BuildDirectory, [string]$ReceiptPath,
    [ValidateRange(1, 3600)][int]$ModuleDeadlineSeconds = 600,
    [ValidateRange(1, 86400)][int]$TotalDeadlineSeconds = 14400) {
  $started = [DateTime]::UtcNow.ToString('o')
  $clock = [Diagnostics.Stopwatch]::StartNew()
  $manifest = Assert-OPT1ReplaySources $RepoRoot $LeanPath
  $initial = Assert-OPT1ProfileSourceEntries $RepoRoot $manifest
  $build = [IO.Path]::GetFullPath($BuildDirectory)
  if ([IO.Directory]::Exists($build) -or [IO.File]::Exists($build)) {
    throw 'OPT1-PROFILE: canonical compilation requires a new private build directory'
  }
  [void][IO.Directory]::CreateDirectory($build)
  foreach ($entry in @($manifest.Sources) + @($manifest.Configuration)) {
    $target = Join-Path $build $entry.Path
    [void][IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($target))
    $canonical = Get-OPT1ProfileCanonicalBytes ([IO.File]::ReadAllBytes((Join-Path $RepoRoot $entry.Path))) $entry.Path
    if ((Get-OPT1ProfileHash $canonical) -cne $entry.CanonicalSHA256) { throw 'OPT1-PROFILE: source changed during materialization' }
    [IO.File]::WriteAllBytes($target, $canonical)
  }
  . (Join-Path $build 'scripts/owned_process_tree.ps1')
  $cache = Join-Path $build '.lake/build/lib/lean'
  $logRoot = Join-Path $build '.lake/profile-process'
  $modules = [Collections.Generic.List[object]]::new()
  $receipt = [ordered]@{
    Version='opt1-r1-build-receipt-v1'; Completed=$false; SourceCommit=$manifest.SourceCommit
    SourceProfileSHA256=Get-OPT1ProfileHash ([IO.File]::ReadAllBytes((Join-Path $RepoRoot 'docs/internal/extensions/opt1/repair-r1/profile/SOURCE_PROFILE.json')))
    BuilderCanonicalSHA256=Get-OPT1ProfileHash (Get-OPT1ProfileCanonicalBytes ([IO.File]::ReadAllBytes((Join-Path $RepoRoot 'scripts/packed_optimized_replay_profile.ps1'))) 'profile builder')
    CanonicalBuildProfile=$manifest.CanonicalBuildProfile; StartedUTC=$started
    Host=[Environment]::OSVersion.VersionString; LeanPath=[IO.Path]::GetFullPath($LeanPath)
    BuildDirectory=$build; ModuleDeadlineSeconds=$ModuleDeadlineSeconds
    TotalDeadlineSeconds=$TotalDeadlineSeconds; OutputLimitBytes=4194304
    Modules=@(); RuntimeImports=@(); Failure=$null; DurationSeconds=0
  }
  try {
    $outputs = @{}
    $toolRoot = [IO.Path]::GetDirectoryName([IO.Path]::GetDirectoryName([IO.Path]::GetFullPath($LeanPath)))
    foreach ($module in $manifest.BuildOrder) {
      $entry = @($manifest.Sources | Where-Object { $_.Module -ceq $module })[0]
      $dependencies = @(foreach ($dependency in (@('Init') + @($entry.Imports))) {
        $path = if ($dependency.StartsWith('RMQ.', [StringComparison]::Ordinal)) {
          Join-Path $cache ($dependency.Replace('.', '/') + '.olean')
        } else { Join-Path $toolRoot ('lib/lean/' + $dependency.Replace('.', '/') + '.olean') }
        if (-not [IO.File]::Exists($path)) { throw "OPT1-PROFILE: direct prerequisite missing before compilation: $dependency" }
        $hash = (Get-FileHash -Algorithm SHA256 -LiteralPath $path).Hash.ToLowerInvariant()
        if ($dependency.StartsWith('RMQ.', [StringComparison]::Ordinal) -and $hash -cne $outputs[$dependency]) {
          throw "OPT1-PROFILE: compiled prerequisite changed: $dependency"
        }
        [pscustomobject]@{ Module=$dependency; ArtifactSHA256=$hash }
      })
      $relativeArtifact = '.lake/build/lib/lean/' + $module.Replace('.', '/') + '.olean'
      $artifact = Join-Path $build $relativeArtifact
      [void][IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($artifact))
      $remaining = $TotalDeadlineSeconds - [int][Math]::Ceiling($clock.Elapsed.TotalSeconds)
      if ($remaining -le 0) { throw 'OPT1-PROFILE: total build deadline reached before launch' }
      $sourceBefore = (Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $build $entry.Path)).Hash.ToLowerInvariant()
      if ($sourceBefore -cne $entry.CanonicalSHA256) { throw "OPT1-PROFILE: canonical source changed before compilation: $module" }
      $arguments = @('-j1', '-o', $relativeArtifact, $entry.Path)
      $result = Invoke-RMQOwnedBoundedProcess -FilePath $LeanPath -Arguments $arguments -WorkingDirectory $build `
        -Stage $module -DeadlineSeconds ([Math]::Min($ModuleDeadlineSeconds, $remaining)) `
        -OutputLimitBytes 4194304 -TempRoot $logRoot -Environment @{ LEAN_PATH=$cache }
      $sourceAfter = (Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $build $entry.Path)).Hash.ToLowerInvariant()
      $artifactHash = if ([IO.File]::Exists($artifact)) { (Get-FileHash -Algorithm SHA256 -LiteralPath $artifact).Hash.ToLowerInvariant() } else { '' }
      $record = [pscustomobject]@{
        Module=$module; Source=$entry.Path; SourceBeforeSHA256=$sourceBefore; SourceAfterSHA256=$sourceAfter
        Dependencies=@($dependencies); Arguments=$arguments; Artifact=$relativeArtifact; ArtifactSHA256=$artifactHash; Result=$result
      }
      $modules.Add($record)
      Write-OPT1ProfileJson (Join-Path $logRoot ($module + '.json')) $record
      $receipt.Modules = @($modules.ToArray())
      $receipt.DurationSeconds = [Math]::Round($clock.Elapsed.TotalSeconds, 3)
      Write-OPT1ProfileJson (Join-Path $build 'BUILD_ATTEMPT.json') $receipt
      Write-Host "OPT1-PROFILE BUILD $($modules.Count)/$($manifest.BuildOrder.Count) $module exit=$($result.ExitCode) seconds=$($result.DurationSeconds)"
      if ($result.ExitCode -ne 0 -or $result.TimedOut -or $result.OutputLimitExceeded -or
          $sourceAfter -cne $sourceBefore -or $artifactHash -ceq '' -or
          ($result.Output -join "`n") -match 'declaration uses .sorry.') {
        throw "OPT1-PROFILE: canonical module compilation failed: $module"
      }
      $outputs[$module] = $artifactHash
    }
    $final = Assert-OPT1ProfileSourceEntries $RepoRoot $manifest
    foreach ($path in $initial.Keys) {
      if ($final[$path] -cne $initial[$path]) { throw "OPT1-PROFILE: original source bytes changed during build: $path" }
    }
    $null = Assert-OPT1ProfileSourceEntries $build $manifest
    $null = Assert-OPT1ProfileToolchain $LeanPath $manifest
    $receipt.RuntimeImports = @(foreach ($module in $manifest.RuntimeImports) {
      [pscustomobject]@{ Module=$module; Source=$module.Replace('.', '/') + '.lean'
        Artifact='.lake/build/lib/lean/' + $module.Replace('.', '/') + '.olean'; ArtifactSHA256=$outputs[$module] }
    })
    $receipt.Completed = $true
    Assert-OPT1ProfileArtifacts $cache $manifest ([pscustomobject]$receipt)
  } catch {
    $receipt.Completed = $false
    $receipt.Failure = $_.Exception.Message
    throw
  } finally {
    $receipt.Modules = @($modules.ToArray())
    $receipt.DurationSeconds = [Math]::Round($clock.Elapsed.TotalSeconds, 3)
    Write-OPT1ProfileJson (Join-Path $build 'BUILD_ATTEMPT.json') $receipt
    Write-OPT1ProfileJson $ReceiptPath $receipt
  }
  return [pscustomobject]@{ ReceiptPath=[IO.Path]::GetFullPath($ReceiptPath)
    ReceiptSHA256=(Get-FileHash -Algorithm SHA256 -LiteralPath $ReceiptPath).Hash.ToLowerInvariant()
    ArtifactDirectory=$cache; ModuleCount=$modules.Count; DurationSeconds=$receipt.DurationSeconds }
}
