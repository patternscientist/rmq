param([string]$SpecPath, [string]$ReleasePath)
$ErrorActionPreference = 'Stop'
while (-not (Test-Path -LiteralPath $ReleasePath -PathType Leaf)) {
  Start-Sleep -Milliseconds 10
}
$spec = Get-Content -LiteralPath $SpecPath -Raw | ConvertFrom-Json
foreach ($property in $spec.Environment.PSObject.Properties) {
  [Environment]::SetEnvironmentVariable(
    $property.Name, [string]$property.Value, 'Process')
}
& ([string]$spec.FilePath) @([string[]]$spec.Arguments)
if ($null -eq $LASTEXITCODE) { exit 0 }
exit ([int]$LASTEXITCODE)