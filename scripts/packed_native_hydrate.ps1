param(
  [string]$SourceRoot = 'C:/Users/poin/.codex/worktrees/2fb8/RMQ'
)
$ErrorActionPreference = 'Stop'
$taskRoot = Split-Path $PSScriptRoot -Parent
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
