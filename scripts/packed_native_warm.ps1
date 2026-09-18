param(
  [string]$Module = 'RMQ.Core.WordRAM.Packed.Capstone',
  [ValidateRange(1, 1000)][int]$StopAfter = 20,
  [ValidateRange(60, 3600)][int]$ModuleDeadlineSeconds = 1200
)
$ErrorActionPreference = 'Stop'
$taskRoot = Split-Path $PSScriptRoot -Parent
$taskLeanRoot = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0'
$taskLake = Join-Path $taskLeanRoot 'bin/lake.exe'
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
if ([IO.File]::ReadAllText((Join-Path $taskRoot 'lean-toolchain')).Trim() -cne 'leanprover/lean4:v4.22.0') {
  throw 'Repository Lean pin changed.'
}
$taskSeen = @{}
$taskOrder = [Collections.Generic.List[string]]::new()
function Visit-NativeDependency([string]$Name) {
  if ($taskSeen.ContainsKey($Name)) { return }
  if ($Name -cnotmatch '^RMQ(\.[A-Za-z0-9_]+)+$') { throw "Unexpected local module: $Name" }
  $taskSeen[$Name] = $true
  $source = Join-Path $taskRoot ($Name.Replace('.', '/') + '.lean')
  if (-not [IO.File]::Exists($source)) { throw "Missing local module: $Name" }
  foreach ($match in [regex]::Matches([IO.File]::ReadAllText($source), '(?m)^import\s+([^\r\n]+)')) {
    foreach ($dependency in ($match.Groups[1].Value.Trim() -split '\s+')) {
      if ($dependency.StartsWith('RMQ.')) { Visit-NativeDependency $dependency }
    }
  }
  $taskOrder.Add($Name)
}
Visit-NativeDependency $Module
$taskInputs = @($taskOrder | ForEach-Object {
  $source = Join-Path $taskRoot ($_.Replace('.', '/') + '.lean')
  [ordered]@{ module = $_; sha256 = (Get-FileHash -LiteralPath $source -Algorithm SHA256).Hash }
})
$taskOut = Join-Path $taskRoot 'docs/internal/extensions/native1/commands'
$taskTmp = Join-Path $taskRoot '.lake/native1/warm'
[void](New-Item -ItemType Directory -Force -Path $taskOut, $taskTmp)
$taskKey = $Module.Replace('.', '-')
$taskProgress = Join-Path $taskTmp ($taskKey + '.json')
$taskNext = 0
if (Test-Path -LiteralPath $taskProgress) {
  $previous = [IO.File]::ReadAllText($taskProgress) | ConvertFrom-Json
  if (($previous.inputs | ConvertTo-Json -Depth 4 -Compress) -cne
      ($taskInputs | ConvertTo-Json -Depth 4 -Compress)) { throw 'Dependency sources changed; inspect before resuming.' }
  $taskNext = [int]$previous.next
}
$taskStamp = [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')
$taskReceipt = Join-Path $taskOut ('warm-' + $taskStamp + '.json')
$taskResults = [Collections.Generic.List[object]]::new()
$taskOldPath = $env:PATH
$taskOldThreads = $env:LEAN_NUM_THREADS
try {
  $env:PATH = (Join-Path $taskLeanRoot 'bin') + ';' + $taskOldPath
  $env:LEAN_NUM_THREADS = '1'
  $taskEnd = [Math]::Min($taskNext + $StopAfter, $taskOrder.Count)
  while ($taskNext -lt $taskEnd) {
    if (Test-Path -LiteralPath (Join-Path $taskTmp 'pause-request')) {
      Write-Output 'NATIVE1-WARM yielding at a completed module boundary'
      break
    }
    $name = $taskOrder[$taskNext]
    $taskStartedUtc = [DateTime]::UtcNow.ToString('o')
    $result = Invoke-RMQOwnedBoundedProcess -FilePath $taskLake -Arguments @('build', ('+' + $name + ':leanArts')) `
      -WorkingDirectory $taskRoot -Stage ('native-warm-' + $name) -DeadlineSeconds $ModuleDeadlineSeconds `
      -OutputLimitBytes 8388608 -TempRoot $taskTmp
    $taskResults.Add([ordered]@{ module = $name; startedUtc = $taskStartedUtc
      completedUtc = [DateTime]::UtcNow.ToString('o'); result = $result })
    [IO.File]::WriteAllText($taskReceipt, ([ordered]@{
      schema = 'native1-warm-v1'; target = $Module; inputs = $taskInputs
      lean = $taskLeanRoot; threads = 1; results = @($taskResults.ToArray())
    } | ConvertTo-Json -Depth 16), [Text.UTF8Encoding]::new($false))
    Write-Output ("NATIVE1-WARM {0}/{1} {2} exit={3} seconds={4}" -f
      ($taskNext + 1), $taskOrder.Count, $name, $result.ExitCode, $result.DurationSeconds)
    if ($result.ExitCode -ne 0 -or $result.TimedOut -or $result.OutputLimitExceeded) {
      $result.Output | Select-Object -Last 20 | Write-Output
      throw "Scoped dependency build failed: $name; inspect $taskReceipt before retrying."
    }
    foreach ($taskInputPin in $taskInputs) {
      $source = Join-Path $taskRoot ($taskInputPin.module.Replace('.', '/') + '.lean')
      if ((Get-FileHash -LiteralPath $source -Algorithm SHA256).Hash -cne $taskInputPin.sha256) {
        throw "Source changed during scoped build: $($taskInputPin.module)"
      }
    }
    $taskNext++
    [IO.File]::WriteAllText($taskProgress, ([ordered]@{
      inputs = $taskInputs; next = $taskNext; lastReceipt = $taskReceipt
    } | ConvertTo-Json -Depth 6), [Text.UTF8Encoding]::new($false))
  }
  Write-Output ("NATIVE1-WARM batch complete next={0} total={1}" -f $taskNext, $taskOrder.Count)
} finally {
  $env:PATH = $taskOldPath
  $env:LEAN_NUM_THREADS = $taskOldThreads
}
