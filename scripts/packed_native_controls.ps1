param()
$ErrorActionPreference = 'Stop'
$controlRoot = Split-Path $PSScriptRoot -Parent
$controlRoute = Join-Path $PSScriptRoot 'packed_native_route.ps1'
$controlIds = @('empty','whitespace','malformed','unknown','source-manifest-missing',
  'artifact-manifest-empty','fixture-manifest-missing','restored-smoke')
$controlResults = [Collections.Generic.List[object]]::new()
function Expect-RouteRejection([string]$Id, [string]$Selector, [string]$Message) {
  $rejected = $false
  try { & $controlRoute -Case $Selector } catch {
    if ($_.Exception.Message -cne $Message) { throw }
    $rejected = $true
  }
  if (-not $rejected) { throw ('control unexpectedly accepted: ' + $Id) }
  $controlResults.Add(@{id=$Id; verdict='expected rejection'; surface=$Message})
  Write-Output ('NATIVE1-CONTROL PASS ' + $Id)
}
$controlSuccess = $false
try {
  Expect-RouteRejection 'empty' '' 'invalid exact selector'
  Expect-RouteRejection 'whitespace' '   ' 'invalid exact selector'
  Expect-RouteRejection 'malformed' 'n9-full,n9-empty' 'invalid exact selector'
  Expect-RouteRejection 'unknown' 'unknown' 'invalid exact selector'
  foreach ($id in @('source-manifest-missing','artifact-manifest-empty','fixture-manifest-missing')) {
    $path = if ($id -eq 'fixture-manifest-missing') {
      Join-Path $controlRoot 'native/packed-rmq/fixtures/manifest.json'
    } else { Join-Path $controlRoot '.lake/native1/build/build-manifest.json' }
    $saved = [IO.File]::ReadAllBytes($path)
    $hash = (Get-FileHash $path).Hash
    try {
      $manifest = [Text.UTF8Encoding]::new($false,$true).GetString($saved) | ConvertFrom-Json
      if ($id -eq 'source-manifest-missing') {
        $manifest.sources = @($manifest.sources | Where-Object { $_.path -cne 'RMQ/Core/WordRAM/Native/Thin.lean' })
      } elseif ($id -eq 'artifact-manifest-empty') {
        $manifest.artifacts = @()
      } else { $manifest.files = @($manifest.files | Select-Object -Skip 1) }
      [IO.File]::WriteAllText($path, ($manifest | ConvertTo-Json -Depth 12), [Text.UTF8Encoding]::new($false))
      $message = if ($id -eq 'fixture-manifest-missing') { 'exact fixture manifest mismatch' } else { 'build manifest shape' }
      Expect-RouteRejection $id 'smoke' $message
    } finally {
      [IO.File]::WriteAllBytes($path, $saved)
      if ((Get-FileHash $path).Hash -cne $hash) { throw ('control restoration failed: ' + $id) }
    }
  }
  & $controlRoute -Case 'smoke'
  $controlResults.Add(@{id='restored-smoke';verdict='expected accept';surface='exact native smoke output'})
  if (($controlResults.id -join ',') -cne ($controlIds -join ',')) { throw 'exact controls registry mismatch' }
  $controlSuccess = $true
} finally {
  $record = @{schema='native1-route-controls-v1';success=$controlSuccess;
    expectedCases=$controlIds;executedCases=@($controlResults.id);results=@($controlResults.ToArray())}
  $outDir = Join-Path $controlRoot 'docs/internal/extensions/native1/commands'
  [void](New-Item -ItemType Directory -Force -Path $outDir)
  [IO.File]::WriteAllText((Join-Path $outDir ('controls-' + [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff') + '.json')),
    ($record | ConvertTo-Json -Depth 12), [Text.UTF8Encoding]::new($false))
}
