param(
  [string]$SourceRoot = 'C:/Users/poin/.codex/worktrees/2fb8/RMQ',
  [switch]$DefaultRMQ
)
$ErrorActionPreference = 'Stop'
$taskRoot = Split-Path $PSScriptRoot -Parent

function Invoke-DefaultRMQHydration {
  # This optional, frozen preparation never invokes Lean or Lake. The original
  # 249-module canonical mode below remains the default.
  $cacheSourceRoot = [IO.Path]::GetFullPath($SourceRoot).TrimEnd('/','\')
  $cacheRoot = [IO.Path]::GetFullPath($taskRoot).TrimEnd('/','\')
  $cacheBuildRoot = [IO.Path]::GetFullPath((Join-Path $cacheRoot '.lake/build'))
  $cacheExpectedSource = [IO.Path]::GetFullPath('C:/Users/poin/.codex/worktrees/2fb8/RMQ')
  if (-not $cacheSourceRoot.Equals($cacheExpectedSource, [StringComparison]::OrdinalIgnoreCase) -or
      $cacheSourceRoot.Equals($cacheRoot, [StringComparison]::OrdinalIgnoreCase)) {
    throw 'Default RMQ preparation requires the distinct registered 2fb8 source checkout.'
  }
  $cacheStarted = [DateTime]::UtcNow
  $cacheReceipt = Join-Path $cacheRoot ('docs/internal/extensions/native1/commands/hydrate-default-' +
    $cacheStarted.ToString('yyyyMMddTHHmmssfff') + '.json')
  $cachePins = [Collections.Generic.List[object]]::new()
  $cachePlan = [Collections.Generic.List[object]]::new()
  $cacheEntries = [Collections.Generic.List[object]]::new()
  $cacheSeen = [Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  $cacheExternal = [Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  $cacheNativeCount = 0
  $cacheExisting = 0
  $cacheSuccess = $false
  $cacheFailure = $null
  $cacheToolchainPins = @()
  $cacheSourceHead = $null
  $cacheCompilerMarker = 'Lean 4.22.0, commit ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05'

  function Get-DefaultHydrationHash([string]$Path) {
    $stream = [IO.FileStream]::new($Path, [IO.FileMode]::Open, [IO.FileAccess]::Read,
      [IO.FileShare]::Read, 1048576, [IO.FileOptions]::SequentialScan)
    $hasher = [Security.Cryptography.SHA256]::Create()
    try { return [BitConverter]::ToString($hasher.ComputeHash($stream)).Replace('-', '') }
    finally { $hasher.Dispose(); $stream.Dispose() }
  }

  function Get-DefaultImportHeader([string]$Text) {
    $cursor = 0
    $imports = [Collections.Generic.List[string]]::new()
    $importPattern = [regex]::new('\Gimport[ \t]+([A-Za-z_][A-Za-z0-9_.]*(?:[ \t]+[A-Za-z_][A-Za-z0-9_.]*)*)')
    $preludePattern = [regex]::new('\Gprelude\b')
    while ($cursor -lt $Text.Length) {
      if ([char]::IsWhiteSpace($Text[$cursor])) { $cursor++; continue }
      if ($cursor + 1 -lt $Text.Length -and $Text.Substring($cursor, 2) -eq '--') {
        $endLine = $Text.IndexOf("`n", $cursor)
        if ($endLine -lt 0) { break }
        $cursor = $endLine + 1
        continue
      }
      if ($cursor + 1 -lt $Text.Length -and $Text.Substring($cursor, 2) -eq '/-') {
        $depth = 1
        $cursor += 2
        while ($depth -gt 0) {
          $nextOpen = $Text.IndexOf('/-', $cursor, [StringComparison]::Ordinal)
          $nextClose = $Text.IndexOf('-/', $cursor, [StringComparison]::Ordinal)
          if ($nextClose -lt 0) { throw 'Unterminated comment in import header.' }
          if ($nextOpen -ge 0 -and $nextOpen -lt $nextClose) { $depth++; $cursor=$nextOpen+2 }
          else { $depth--; $cursor=$nextClose+2 }
        }
        continue
      }
      $prelude = $preludePattern.Match($Text, $cursor)
      if ($prelude.Success) { $cursor += $prelude.Length; continue }
      $declaration = $importPattern.Match($Text, $cursor)
      if (-not $declaration.Success) { break }
      foreach ($name in ($declaration.Groups[1].Value -split '\s+')) { $imports.Add($name) }
      $cursor += $declaration.Length
    }
    return $imports.ToArray()
  }

  function Read-DefaultModule([string]$Module) {
    if (-not $cacheSeen.Add($Module)) { return }
    if ($Module -notmatch '^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$') {
      throw "Unsupported import token: $Module"
    }
    $relative = $Module.Replace('.', '/') + '.lean'
    $localSource = Join-Path $cacheRoot $relative
    if (-not [IO.File]::Exists($localSource)) {
      if ($Module -notmatch '^(Init|Lean|Std)(\.|$)') {
        throw "Missing local import: $Module"
      }
      [void]$cacheExternal.Add($Module)
      return
    }
    $localHash = Get-DefaultHydrationHash $localSource
    $sourceText = [IO.File]::ReadAllText($localSource, [Text.UTF8Encoding]::new($false, $true))
    foreach ($dependency in (Get-DefaultImportHeader $sourceText)) { Read-DefaultModule $dependency }
    $foreignSource = Join-Path $cacheSourceRoot $relative
    if ((Get-DefaultHydrationHash $foreignSource) -cne $localHash) {
      throw "Default RMQ source differs: $relative"
    }
    $cachePins.Add([ordered]@{module=$Module;path=$relative;sha256Before=$localHash})
  }

  function Assert-LocalDestination([string]$Relative) {
    $destination = [IO.Path]::GetFullPath((Join-Path $cacheRoot $Relative))
    if (-not $destination.StartsWith($cacheBuildRoot + [IO.Path]::DirectorySeparatorChar,
        [StringComparison]::OrdinalIgnoreCase)) { throw "Destination escaped build tree: $destination" }
    $ancestor = Split-Path $destination -Parent
    while ($ancestor.Length -ge $cacheRoot.Length) {
      if (Test-Path -LiteralPath $ancestor) {
        $item = Get-Item -LiteralPath $ancestor -Force
        if (($item.Attributes -band [IO.FileAttributes]::ReparsePoint) -ne 0) {
          throw "Destination traverses a link: $ancestor"
        }
      }
      if ($ancestor.Equals($cacheRoot, [StringComparison]::OrdinalIgnoreCase)) { break }
      $ancestor = Split-Path $ancestor -Parent
    }
    return $destination
  }

  try {
    $registered = @(git -C $cacheRoot worktree list --porcelain)
    if ($LASTEXITCODE -ne 0) { throw 'Cannot inspect registered source checkout.' }
    for ($i = 0; $i -lt $registered.Count; $i++) {
      if ($registered[$i] -eq ('worktree ' + $cacheSourceRoot.Replace('\','/'))) {
        $cacheSourceHead = $registered[$i + 1] -replace '^HEAD ', ''
      }
    }
    if (-not $cacheSourceHead) { throw 'Source checkout is not registered.' }
    $cacheToolchainPins = @(foreach ($rootPath in @($cacheRoot, $cacheSourceRoot)) {
      $pinPath = Join-Path $rootPath 'lean-toolchain'
      if ([IO.File]::ReadAllText($pinPath).Trim() -cne 'leanprover/lean4:v4.22.0') {
        throw "Toolchain pin differs: $pinPath"
      }
      [ordered]@{path=$pinPath;sha256Before=(Get-DefaultHydrationHash $pinPath)}
    })
    if ($cacheToolchainPins[0].sha256Before -cne $cacheToolchainPins[1].sha256Before) {
      throw 'Toolchain source bytes differ.'
    }
    Read-DefaultModule 'RMQ'
    if ($cachePins.Count -ne 372) { throw "Unexpected default closure count: $($cachePins.Count)" }
    $cacheNativeCount = @($cachePins | Where-Object { $_.module -match '^RMQ\.Core\.WordRAM\.Native(\.|$)' }).Count
    if ($cacheNativeCount -ne 0) { throw 'Default root unexpectedly imports Native.' }
    foreach ($pin in $cachePins) {
      $relative = $pin.module.Replace('.', '/')
      $tracePath = Join-Path $cacheSourceRoot ('.lake/build/lib/lean/' + $relative + '.trace')
      if (-not [IO.File]::ReadAllText($tracePath).Contains($cacheCompilerMarker)) {
        throw "Missing expected compiler trace: $tracePath"
      }
      foreach ($artifact in @(('.lake/build/lib/lean/' + $relative + '.olean'),
          ('.lake/build/lib/lean/' + $relative + '.ilean'),
          ('.lake/build/lib/lean/' + $relative + '.trace'), ('.lake/build/ir/' + $relative + '.c'))) {
        $from = Join-Path $cacheSourceRoot $artifact
        if (-not [IO.File]::Exists($from)) { throw "Missing source artifact: $from" }
        $to = Assert-LocalDestination $artifact
        if (Test-Path -LiteralPath $to) { $cacheExisting++; continue }
        $cachePlan.Add([ordered]@{module=$pin.module;path=$artifact;bytes=([IO.FileInfo]$from).Length})
      }
    }
    if ($cachePlan.Count -ne 491) { throw "Unexpected missing artifact count: $($cachePlan.Count); no copying started." }
    $cachePlannedBytes = 0L
    foreach ($entry in $cachePlan) { $cachePlannedBytes += $entry.bytes }
    Write-Output "NATIVE1-DEFAULT-HYDRATE planned=491 modules=372 native=0 bytes=$cachePlannedBytes"
    foreach ($entry in $cachePlan) {
      $from = Join-Path $cacheSourceRoot $entry.path
      $to = Assert-LocalDestination $entry.path
      $before = Get-DefaultHydrationHash $from
      [void][IO.Directory]::CreateDirectory((Split-Path $to -Parent))
      [IO.File]::Copy($from, $to, $false)
      $after = Get-DefaultHydrationHash $from
      $destinationHash = Get-DefaultHydrationHash $to
      $cacheEntries.Add([ordered]@{module=$entry.module;path=$entry.path;bytes=$entry.bytes
        sourceSHA256Before=$before;sourceSHA256After=$after;destinationSHA256=$destinationHash})
      if ($before -cne $after -or $destinationHash -cne $before) { throw "Artifact changed during copying: $from" }
      if ($cacheEntries.Count % 50 -eq 0) { Write-Output "NATIVE1-DEFAULT-HYDRATE copied=$($cacheEntries.Count)/491" }
    }
    foreach ($pin in $cachePins) {
      $localAfter = Get-DefaultHydrationHash (Join-Path $cacheRoot $pin.path)
      $foreignAfter = Get-DefaultHydrationHash (Join-Path $cacheSourceRoot $pin.path)
      $pin.localSHA256After = $localAfter
      $pin.sourceSHA256After = $foreignAfter
      if ($localAfter -cne $pin.sha256Before -or $foreignAfter -cne $pin.sha256Before) {
        throw "Source changed while copying: $($pin.path)"
      }
    }
    foreach ($pin in $cacheToolchainPins) {
      $pin.sha256After = Get-DefaultHydrationHash $pin.path
      if ($pin.sha256After -cne $pin.sha256Before) { throw 'Toolchain pin changed during copying.' }
    }
    $cacheSuccess = $true
  } catch {
    $cacheFailure = $_.Exception.Message
    throw
  } finally {
    $record = [ordered]@{schema='native1-default-artifact-copy-v1';success=$cacheSuccess
      failure=$cacheFailure;sourceRoot=$cacheSourceRoot;sourceHead=$cacheSourceHead;destinationRoot=$cacheRoot
      startedUtc=$cacheStarted.ToString('o');completedUtc=[DateTime]::UtcNow.ToString('o')
      helperSHA256=(Get-DefaultHydrationHash $PSCommandPath)
      target='RMQ';closureCount=$cachePins.Count;nativeModules=$cacheNativeCount
      toolchains=$cacheToolchainPins;compilerTraceMarker=$cacheCompilerMarker;hashReadBufferBytes=1048576
      sources=@($cachePins.ToArray());externalImports=@($cacheExternal | Sort-Object)
      plannedArtifacts=@($cachePlan.ToArray());artifacts=@($cacheEntries.ToArray())
      copied=$cacheEntries.Count;preexistingArtifactsPreserved=$cacheExisting
      linksCreated=0;existingFilesOverwritten=0;leanInvoked=$false;lakeInvoked=$false
      nextRequiredCommand='lake --no-build build RMQ'
      validationStatus='PENDING: cache preparation does not certify the default build.'}
    [IO.File]::WriteAllText($cacheReceipt, ($record | ConvertTo-Json -Depth 8), [Text.UTF8Encoding]::new($false))
  }
  Write-Output "NATIVE1-DEFAULT-HYDRATE copied=$($cacheEntries.Count) receipt=$cacheReceipt"
}

if ($DefaultRMQ) {
  Invoke-DefaultRMQHydration
  return
}

$taskProgress = Join-Path $taskRoot '.lake/native1/warm/RMQ-Core-WordRAM-Packed-Capstone.json'
$taskPins = ([IO.File]::ReadAllText($taskProgress) | ConvertFrom-Json).inputs
if ($taskPins.Count -ne 249) { throw 'Unexpected frozen canonical dependency closure.' }
$taskSourceRoot = [IO.Path]::GetFullPath($SourceRoot)
if ($taskSourceRoot -eq [IO.Path]::GetFullPath($taskRoot)) { throw 'Source must be a distinct checkout.' }
if ([IO.File]::ReadAllText((Join-Path $taskSourceRoot 'lean-toolchain')).Trim() -cne
    'leanprover/lean4:v4.22.0') { throw 'Source compiler pin differs.' }
$taskEntries = [Collections.Generic.List[object]]::new()
$taskEligible = [Collections.Generic.List[object]]::new()
$taskSkipped = [Collections.Generic.List[string]]::new()
$taskStarted = [DateTime]::UtcNow.ToString('o')
$taskSuccess = $false
$taskReceipt = Join-Path $taskRoot ('docs/internal/extensions/native1/commands/hydrate-' +
  [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff') + '.json')
try {
  foreach ($taskPin in $taskPins) {
    $taskRelative = $taskPin.module.Replace('.', '/')
    $taskLocalSource = Join-Path $taskRoot ($taskRelative + '.lean')
    $taskForeignSource = Join-Path $taskSourceRoot ($taskRelative + '.lean')
    if ((Get-FileHash -LiteralPath $taskLocalSource -Algorithm SHA256).Hash -cne $taskPin.sha256) {
      throw "Local dependency source differs: $taskLocalSource"
    }
    if ((Get-FileHash -LiteralPath $taskForeignSource -Algorithm SHA256).Hash -cne $taskPin.sha256) {
      $taskSkipped.Add($taskPin.module)
      continue
    }
    $taskTracePath = Join-Path $taskSourceRoot ('.lake/build/lib/lean/' + $taskRelative + '.trace')
    $taskTrace = [IO.File]::ReadAllText($taskTracePath)
    if (-not $taskTrace.Contains('Lean 4.22.0, commit ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05')) {
      throw "Missing expected compiler trace: $taskTracePath"
    }
    $taskEligible.Add($taskPin)
  }
  foreach ($taskPin in $taskEligible) {
    $taskRelative = $taskPin.module.Replace('.', '/')
    $taskArtifactPaths = @(('.lake/build/lib/lean/' + $taskRelative + '.olean'),
      ('.lake/build/lib/lean/' + $taskRelative + '.ilean'),
      ('.lake/build/lib/lean/' + $taskRelative + '.trace'),
      ('.lake/build/ir/' + $taskRelative + '.c'))
    foreach ($taskRelativeArtifact in $taskArtifactPaths) {
      $taskFrom = Join-Path $taskSourceRoot $taskRelativeArtifact
      $taskTo = Join-Path $taskRoot $taskRelativeArtifact
      $taskBefore = (Get-FileHash -LiteralPath $taskFrom -Algorithm SHA256).Hash
      $taskCopied = -not (Test-Path -LiteralPath $taskTo)
      if ($taskCopied) {
        [void](New-Item -ItemType Directory -Force -Path (Split-Path $taskTo -Parent))
        [IO.File]::Copy($taskFrom, $taskTo, $false)
      }
      $taskAfter = (Get-FileHash -LiteralPath $taskFrom -Algorithm SHA256).Hash
      $taskDestinationHash = (Get-FileHash -LiteralPath $taskTo -Algorithm SHA256).Hash
      if ($taskAfter -cne $taskBefore -or ($taskCopied -and $taskDestinationHash -cne $taskBefore)) {
        throw "Artifact changed during copy: $taskFrom"
      }
      $taskEntries.Add([ordered]@{path=$taskRelativeArtifact;copied=$taskCopied
        sourceSHA256=$taskBefore;destinationSHA256=$taskDestinationHash})
    }
  }
  foreach ($taskPin in $taskEligible) {
    foreach ($taskCheckRoot in @($taskRoot, $taskSourceRoot)) {
      $taskSource = Join-Path $taskCheckRoot ($taskPin.module.Replace('.', '/') + '.lean')
      if ((Get-FileHash -LiteralPath $taskSource -Algorithm SHA256).Hash -cne $taskPin.sha256) {
        throw "Source changed while copying: $taskSource"
      }
    }
  }
  $taskSuccess = $true
} finally {
  $taskRecord = [ordered]@{schema='native1-isolated-artifact-copy-v1';success=$taskSuccess
    sourceRoot=$taskSourceRoot;destinationRoot=$taskRoot;startedUtc=$taskStarted
    completedUtc=[DateTime]::UtcNow.ToString('o');sources=$taskPins
    artifacts=@($taskEntries.ToArray());linksCreated=0;existingFilesOverwritten=0
    skippedSourceMismatches=@($taskSkipped.ToArray())
    nextRequiredCheck='Lake --no-build validates the copied dependency/output hashes before use.'}
  [IO.File]::WriteAllText($taskReceipt,($taskRecord | ConvertTo-Json -Depth 8),[Text.UTF8Encoding]::new($false))
}
Write-Output ('NATIVE1-HYDRATE copied=' + @($taskEntries | Where-Object copied).Count +
  ' examined=' + $taskEntries.Count + ' receipt=' + $taskReceipt)
