# Sequential direct-module development check; final Lake certification is separate.
[CmdletBinding()]
param(
  [string]$PlanPath = 'docs/internal/extensions/opt1/query-build-plan.json',
  [string]$EvidenceDirectory = 'docs/internal/extensions/opt1/query-development',
  [int]$ModuleDeadlineSeconds = 600,
  [int]$TotalDeadlineSeconds = 14400
)
$ErrorActionPreference = 'Stop'
$repo = (Get-Location).Path
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
$lean = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe'
$cache = Join-Path $repo '.lake/build/lib/lean'
$evidence = Join-Path $repo $EvidenceDirectory
$temporary = Join-Path $repo '.lake/opt1-process'
[void](New-Item -ItemType Directory -Force -Path $evidence)
$decoded = Get-Content -LiteralPath (Join-Path $repo $PlanPath) -Raw | ConvertFrom-Json
$modules = @($decoded | ForEach-Object { [string]$_ })
if ($modules.Count -eq 0 -or ($modules | Sort-Object -Unique).Count -ne $modules.Count) {
  throw 'Empty or duplicate module plan'
}
$clock = [Diagnostics.Stopwatch]::StartNew()
$index = 0
foreach ($module in $modules) {
  if (Test-Path -LiteralPath (Join-Path $repo '.lake/opt1-build-pause')) {
    Write-Output "Scoped build paused between modules; completed=$index expected=$($modules.Count)."
    exit 2
  }
  $index++
  if ($module -notmatch '^RMQ(?:\.[A-Za-z_][A-Za-z0-9_]*)+$') { throw "Malformed module $module" }
  $relative = $module.Replace('.', '/')
  $source = Join-Path $repo ($relative + '.lean')
  $artifact = Join-Path $cache ($relative + '.olean')
  $recordPath = Join-Path $evidence ($module + '.json')
  if (-not (Test-Path -LiteralPath $source)) { throw "Missing scoped source $source" }
  $sourceHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $source).Hash
  $reusable = Test-Path -LiteralPath $artifact
  if ($reusable) {
    $artifactTime = (Get-Item -LiteralPath $artifact).LastWriteTimeUtc
    $reusable = $artifactTime -ge (Get-Item -LiteralPath $source).LastWriteTimeUtc
    # A rebuilt direct import invalidates its consumer even when its source is unchanged.
    foreach ($line in Get-Content -LiteralPath $source) {
      if ($line -match '^import\s+(.+)$') {
        foreach ($dependency in ($Matches[1] -split '\s+')) {
          if ($dependency -notmatch '^RMQ(?:\.[A-Za-z_][A-Za-z0-9_]*)+$') { continue }
          $importArtifact = Join-Path $cache ($dependency.Replace('.', '/') + '.olean')
          if (-not (Test-Path -LiteralPath $importArtifact) -or
              (Get-Item -LiteralPath $importArtifact).LastWriteTimeUtc -gt $artifactTime) {
            $reusable = $false
          }
        }
      }
    }
  }
  if ($reusable) {
    # Only this task's isolated cache is used. Every reused artifact is recorded.
    [ordered]@{ Module=$module; Disposition='REUSED_TASK_LOCAL'; SourceSHA256=$sourceHash;
      ArtifactSHA256=(Get-FileHash -Algorithm SHA256 -LiteralPath $artifact).Hash } |
      ConvertTo-Json | Set-Content -Encoding utf8 -LiteralPath (Join-Path $evidence ($module + '.reuse.json'))
    Write-Output "[$index/$($modules.Count)] local artifact $module"
    continue
  }
  $remaining = $TotalDeadlineSeconds - [int][Math]::Ceiling($clock.Elapsed.TotalSeconds)
  if ($remaining -le 0) { throw 'Scoped build total deadline reached before next launch' }
  $deadline = [Math]::Min($ModuleDeadlineSeconds, $remaining)
  [void](New-Item -ItemType Directory -Force -Path ([IO.Path]::GetDirectoryName($artifact)))
  $arguments = @('-j1','-o',$artifact,$source)
  $result = Invoke-RMQOwnedBoundedProcess -FilePath $lean -Arguments $arguments `
    -WorkingDirectory $repo -Stage $module -DeadlineSeconds $deadline `
    -OutputLimitBytes 1048576 -TempRoot $temporary -Environment @{ LEAN_PATH=$cache }
  $record = [ordered]@{ Module=$module; Command=@($lean)+$arguments; SourceSHA256=$sourceHash;
    Base='0e6a00f654abc64f8b68988fa9675b9a839dca2f';
    Platform=[Environment]::OSVersion.VersionString; Result=$result } | ConvertTo-Json -Depth 7
  $record | Set-Content -Encoding utf8 -LiteralPath $recordPath
  # Retain every attempt even when a later repaired source updates the latest receipt.
  $archiveName = $module + '.' + [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfffffffZ') + '.json'
  $record | Set-Content -Encoding utf8 -LiteralPath (Join-Path $evidence $archiveName)
  Write-Output "[$index/$($modules.Count)] $module exit=$($result.ExitCode) timeout=$($result.TimedOut)"
  if ($result.ExitCode -ne 0 -or $result.TimedOut -or $result.OutputLimitExceeded) { exit 1 }
}
Write-Output "Scoped module plan finished: $index/$($modules.Count). Final aggregate not run."
