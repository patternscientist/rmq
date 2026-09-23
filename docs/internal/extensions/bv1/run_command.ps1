param(
  [Parameter(Mandatory=$true)][string]$Stage,
  [Parameter(Mandatory=$true)][string]$Executable,
  [string[]]$CommandArguments = @(),
  [int]$DeadlineSeconds = 900
)
$ErrorActionPreference = 'Stop'
$repo = (Resolve-Path (Join-Path $PSScriptRoot '../../../..')).Path
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
$logs = Join-Path $PSScriptRoot 'commands'
[void](New-Item -ItemType Directory -Path $logs -Force)
if ($Stage -notmatch '^[a-z0-9-]+$') { throw 'Stage must be a simple lowercase evidence identifier.' }
$recordPath = Join-Path $logs ($Stage + '.json')
if (Test-Path -LiteralPath $recordPath) { throw 'Evidence stage already exists; choose a new stage name.' }
$toolBin = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin'
$head = (& git -C $repo rev-parse HEAD).Trim()
$dirty = @(& git -C $repo status --porcelain=v1)
$sourceHashes = @((Get-ChildItem -LiteralPath (Join-Path $repo 'RMQ/Core/WordRAM/Bitvector') -Filter '*.lean' -Recurse),
  (Get-ChildItem -LiteralPath (Join-Path $repo 'scripts') -Filter 'packed_bitvector_*'),
  (Get-Item -LiteralPath (Join-Path $repo 'RMQ/Validation/PackedBitvector.lean')),
  (Get-Item -LiteralPath (Join-Path $repo 'lakefile.toml'))) |
  ForEach-Object { Get-FileHash -LiteralPath $_.FullName -Algorithm SHA256 } |
  Select-Object Path, Hash
$startedUtc = [DateTime]::UtcNow.ToString('o')
$result = Invoke-RMQOwnedBoundedProcess -FilePath $Executable -Arguments $CommandArguments `
  -WorkingDirectory $repo -Stage $Stage -DeadlineSeconds $DeadlineSeconds `
  -OutputLimitBytes 8388608 -TempRoot $logs `
  -Environment @{ PATH = $toolBin + ';' + $env:PATH; LEAN_NUM_THREADS = '1' }
$record = [ordered]@{
  stage = $Stage; platform = 'Windows'; head = $head; dirty = $dirty
  sourceHashes = @($sourceHashes); startedUtc = $startedUtc
  executable = $Executable; arguments = $CommandArguments
  deadlineSeconds = $DeadlineSeconds; leanNumThreads = 1; result = $result
}
[IO.File]::WriteAllText($recordPath,
  ($record | ConvertTo-Json -Depth 12), [Text.UTF8Encoding]::new($false))
$result | ConvertTo-Json -Depth 8
if ($result.TimedOut) { exit 124 }
if ($result.OutputLimitExceeded) { exit 125 }
exit $result.ExitCode
