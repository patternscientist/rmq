param(
  [string]$Stage = ('frozen-rows-' + [DateTime]::UtcNow.ToString('yyyyMMddHHmmssfff'))
)
$ErrorActionPreference = 'Stop'
if ($Stage -notmatch '^[a-z0-9-]+$') { throw 'Invalid evidence stage.' }
$repo = (Resolve-Path (Join-Path $PSScriptRoot '../../../..')).Path
$base = '645a0502b9da9ad6444edbe44759e1c2c5661f25'
$relative = 'docs/internal/extensions/bv1/ACCEPTANCE_MATRIX.md'
$record = Join-Path $PSScriptRoot ('commands/' + $Stage + '.json')
if (Test-Path -LiteralPath $record) { throw 'Evidence already exists.' }
$utf8 = [Text.UTF8Encoding]::new($false, $true)
$process = [Diagnostics.Process]::new()
$process.StartInfo.FileName = (Get-Command git).Source
$process.StartInfo.WorkingDirectory = $repo
$process.StartInfo.UseShellExecute = $false
$process.StartInfo.CreateNoWindow = $true
$process.StartInfo.RedirectStandardOutput = $true
$process.StartInfo.RedirectStandardError = $true
foreach ($arg in @('cat-file','blob',($base + ':' + $relative))) {
  [void]$process.StartInfo.ArgumentList.Add($arg)
}
$buffer = [IO.MemoryStream]::new()
try {
  if (-not $process.Start()) { throw 'Could not read frozen Git blob.' }
  $copy = $process.StandardOutput.BaseStream.CopyToAsync($buffer)
  $stderrTask = $process.StandardError.ReadToEndAsync()
  if (-not $process.WaitForExit(30000)) {
    $process.Kill($true)
    $process.WaitForExit()
    throw 'Frozen-blob read exceeded 30 seconds; no passing evidence.'
  }
  [void]$copy.GetAwaiter().GetResult()
  $stderr = $stderrTask.GetAwaiter().GetResult()
  if ($process.ExitCode -ne 0) { throw ('Frozen-blob read failed: ' + $stderr) }
  $baseBytes = $buffer.ToArray()
} finally {
  $buffer.Dispose()
  $process.Dispose()
}
$candidateBytes = [IO.File]::ReadAllBytes((Join-Path $repo $relative))
$baseText = $utf8.GetString($baseBytes)
$candidateText = $utf8.GetString($candidateBytes)
$pattern = '(?m)^\| \x60(?<id>[A-Z0-9-]+)\x60 \|[^\r\n]*'
$expected = @('REQ-BV-ALLOC','REQ-BV-OPS','REQ-BV-RUN','REQ-BV-REUSE','REQ-BV-JOIN',
  'CHK-BV-CONTROLS','INV-STORE-IDENTITY','INV-VALUE-DEPENDENCY','INV-SEMANTIC-NONVACUITY',
  'INV-TRACE-EXECUTION','INV-STORE-AGREEMENT','INV-READ-BACKING','INV-WORD-WIDTH',
  'INV-ADDRESS-WIDTH','INV-INSTRUCTION-ATOMICITY','INV-PROGRAM-ACCOUNTING',
  'INV-ORACLE-INDEPENDENCE','INV-VALIDATION-REACH','INV-ALL-SIZE','INV-PROOF-SEPARATION',
  'INV-NO-SYNTHETIC','INV-CATEGORY-SEPARATION','INV-PUBLIC-COMPOSITION',
  'INV-CERTIFICATE-ANTI-BYPASS','INV-MUTATION-REPRODUCIBILITY','INV-GLOBAL-PHYSICAL-MACHINE',
  'INV-WIDTH-SCALING','REPLAY-EXACT-REGISTRY','REPLAY-SELECTOR-NONVACUITY','REPLAY-SUBPROCESS-DEADLINE')
function Extract-Rows([string]$Value) {
  $rows = [ordered]@{}
  foreach ($match in [regex]::Matches($Value, $pattern)) {
    $id = $match.Groups['id'].Value
    if ($rows.Contains($id)) { throw ('Duplicate frozen row: ' + $id) }
    $rows[$id] = $match.Value
  }
  if ($rows.Count -ne 30 -or ($rows.Keys -join '|') -cne ($expected -join '|')) {
    throw 'Frozen row identity/order/count mismatch.'
  }
  return $rows
}
function Hash-Bytes([byte[]]$Value) {
  return [Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($Value))
}
$baseRows = Extract-Rows $baseText
$candidateRows = Extract-Rows $candidateText
$results = @()
foreach ($id in $expected) {
  $before = $utf8.GetBytes($baseRows[$id])
  $after = $utf8.GetBytes($candidateRows[$id])
  $same = $before.Length -eq $after.Length
  for ($i = 0; $same -and $i -lt $before.Length; $i++) { $same = $before[$i] -eq $after[$i] }
  $results += [ordered]@{id=$id;byteEqual=$same;baseBytes=$before.Length;candidateBytes=$after.Length;
    baseSHA256=(Hash-Bytes $before);candidateSHA256=(Hash-Bytes $after)}
}
$mojibake = $candidateText -match 'Â¬|â€œ|â€|�'
$changed = @($results | Where-Object { -not $_.byteEqual } | ForEach-Object { $_.id })
$fileHash = Hash-Bytes $candidateBytes
$fileUnchanged = $fileHash -ceq '80BD59A314FD33D37076802954444DA24F65C87A2A91DE23BC668B6AF9CCEB24'
$pass = $changed.Count -eq 0 -and -not $mojibake -and $fileUnchanged
[IO.File]::WriteAllText($record, ([ordered]@{
  version=1;stage=$Stage;baseRef=$base;candidateHEAD=(& git -C $repo rev-parse HEAD).Trim();path=$relative;
  strictUTF8=$true;expectedRows=30;checkedRows=$results.Count;changedIds=$changed;mojibake=$mojibake;
  baseBlobSHA256=(Hash-Bytes $baseBytes);candidateFileSHA256=$fileHash;entireFileUnchanged=$fileUnchanged;
  rowDefinition='Complete table-row UTF-8 bytes excluding only its line terminator; no normalization';
  rows=$results;passed=$pass
} | ConvertTo-Json -Depth 8), $utf8)
Write-Output "BV1-FROZEN-ROWS passed=$pass checked=$($results.Count) expected=30 changed=$($changed.Count) fileUnchanged=$fileUnchanged"
if (-not $pass) { exit 1 }
