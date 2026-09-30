[CmdletBinding()]
param()
$ErrorActionPreference = 'Stop'
$strictUtf8 = [Text.UTF8Encoding]::new($false, $true)
$expectedIds = @('LN0-01','LN0-02','LN0-03','LN0-04','LN0-05','LN0-06',
  'INV-SEMANTIC-NONVACUITY','INV-ORACLE-INDEPENDENCE','INV-CATEGORY-SEPARATION',
  'INV-MUTATION-REPRODUCIBILITY','CHK-FINAL','CHK-SCOPE')
$pins = @{
  'ACCEPTANCE_ROWS.txt' = 'F45113AE6BF3F769105A748B3D0A61EA99532A05A715410F11EF29E7E518EC29'
  'REQUIREMENTS.json' = '0983881A85F9A3B42ECD54C0BFB18170C3BE3E5A65602CDE66547042CA5421C9'
}
foreach ($entry in $pins.GetEnumerator()) {
  if ((Get-FileHash -LiteralPath (Join-Path $PSScriptRoot $entry.Key)).Hash -cne $entry.Value) {
    throw "Frozen prompt baseline changed: $($entry.Key)"
  }
}
$requirements = $strictUtf8.GetString([IO.File]::ReadAllBytes(
  (Join-Path $PSScriptRoot 'REQUIREMENTS.json'))) | ConvertFrom-Json
$matrix = $strictUtf8.GetString([IO.File]::ReadAllBytes(
  (Join-Path $PSScriptRoot 'ACCEPTANCE_MATRIX.md')))
$baseline = [IO.File]::ReadAllBytes((Join-Path $PSScriptRoot 'ACCEPTANCE_ROWS.txt'))
$rows = @($matrix.Split("`n") | Where-Object { $_ -match '^\| `(?:LN0-|INV-|CHK-)' })
if ($rows.Count -ne $expectedIds.Count -or $requirements.Count -ne $expectedIds.Count) {
  throw 'Frozen row count changed'
}
$seen = @{}
for ($index=0; $index -lt $rows.Count; $index++) {
  $cells = $rows[$index].Split('|')
  if ($cells.Count -ne 10 -or $cells[0] -cne '' -or $cells[9] -cne '') {
    throw "Expected all eight columns on row $index"
  }
  $id = $cells[1].Trim().Trim('`')
  if ($seen.ContainsKey($id) -or $id -cne $expectedIds[$index] -or
      $id -cne $requirements[$index][0]) { throw "Missing, unknown, duplicate or reordered ID: $id" }
  $seen[$id] = $true
  if ($cells[2].Trim() -cne $requirements[$index][1]) { throw "Full requirement differs: $id" }
}
$candidate = $strictUtf8.GetBytes(($rows -join "`n") + "`n")
if ($candidate.Length -ne $baseline.Length) { throw 'Frozen row byte length differs' }
for ($index=0; $index -lt $baseline.Length; $index++) {
  if ($candidate[$index] -ne $baseline[$index]) { throw "Frozen row byte differs at $index" }
}
Write-Output 'CONTRACT PASS: 12 exact ordered IDs, all eight columns, full prompt requirements, frozen UTF-8 row bytes'
