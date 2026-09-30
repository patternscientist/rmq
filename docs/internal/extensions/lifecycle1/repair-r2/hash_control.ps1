[CmdletBinding()]
param(
  [Parameter(Mandatory=$true)][string]$SourcePath,
  [Parameter(Mandatory=$true)][string]$ExpectedSourceSha256,
  [Parameter(Mandatory=$true)][string]$OutputPath
)
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$utf8=New-Object Text.UTF8Encoding($false,$true)
$vectorPath=Join-Path $PSScriptRoot 'HASH_VECTORS.json'
$vectorHash='6e2f6e3592a715b0dc497184ef38a7345827d9d8f834f7729a143c314ff67080'
function Equal([string]$a,[string]$b){return [string]::Equals($a,$b,[StringComparison]::Ordinal)}
function Require([bool]$condition,[string]$detail){if(-not $condition){throw ('L1R2-HASH: '+$detail)}}
Require (Equal (Get-FileHash -LiteralPath $vectorPath).Hash.ToLowerInvariant() $vectorHash) 'frozen vector bytes changed'
Require (Equal (Get-FileHash -LiteralPath $SourcePath).Hash.ToLowerInvariant() $ExpectedSourceSha256) 'source bytes changed'
$sourceBytes=[IO.File]::ReadAllBytes($SourcePath)
$source=$utf8.GetString($sourceBytes)
$tokens=$null;$errors=$null
$ast=[Management.Automation.Language.Parser]::ParseInput($source,[ref]$tokens,[ref]$errors)
Require (@($errors).Count -eq 0) 'source parse error'
$functions=@($ast.EndBlock.Statements|Where-Object {$_ -is [Management.Automation.Language.FunctionDefinitionAst] -and (Equal $_.Name 'Hash-Bytes')})
Require ($functions.Count -eq 1) 'unique production function missing'
$span=$functions[0].Extent.Text
$start=$utf8.GetByteCount($source.Substring(0,$functions[0].Extent.StartOffset))
$spanBytes=$utf8.GetBytes($span)
$copied=New-Object byte[] $spanBytes.Length
[Array]::Copy($sourceBytes,$start,$copied,0,$copied.Length)
Require (Equal ([Convert]::ToBase64String($copied)) ([Convert]::ToBase64String($spanBytes))) 'AST/raw span mismatch'
Require (-not(Test-Path -LiteralPath $OutputPath)) 'fresh receipt required'
$vector=$utf8.GetString([IO.File]::ReadAllBytes($vectorPath))|ConvertFrom-Json
$expectedIds=@('empty','zero','ff','binary','unicode-utf8','unicode-one-byte','lf','crlf')
Require (@($vector.vectors).Count -eq $expectedIds.Count) 'vector count'
for($i=0;$i -lt $expectedIds.Count;$i++){Require (Equal $vector.vectors[$i].id $expectedIds[$i]) 'vector mapping'}
. ([scriptblock]::Create($span))
$results=[Collections.Generic.List[object]]::new()
$failure=$null;$passed=$false
try {
  foreach($v in $vector.vectors){
    [byte[]]$bytes=New-Object byte[] ($v.hex.Length/2)
    for($i=0;$i -lt $bytes.Length;$i++){$bytes[$i]=[Convert]::ToByte($v.hex.Substring(2*$i,2),16)}
    Require ($bytes.Length -eq $v.bytes) 'exact vector length'
    $actual=@(Hash-Bytes $bytes)
    Require ($actual.Count -eq 1 -and $actual[0] -is [string]) 'one scalar string required'
    Require ([regex]::IsMatch($actual[0],'\A[0-9a-f]{64}\z',[Text.RegularExpressions.RegexOptions]::CultureInvariant)) 'lowercase hexadecimal required'
    Require (Equal $actual[0] $v.sha256) ('independent vector mismatch: '+$v.id)
    $results.Add([ordered]@{id=$v.id;inputHex=$v.hex;bytes=$bytes.Length;actual=$actual[0];expected=$v.sha256;passed=$true})
  }
  foreach($pair in $vector.unequalPairs){
    $a=@($results|Where-Object {Equal $_.id $pair[0]})
    $b=@($results|Where-Object {Equal $_.id $pair[1]})
    Require ($a.Count -eq 1 -and $b.Count -eq 1 -and -not(Equal $a[0].actual $b[0].actual)) 'changed bytes not distinguished'
  }
  Require (Equal (Get-FileHash -LiteralPath $SourcePath).Hash.ToLowerInvariant() $ExpectedSourceSha256) 'source changed during vectors'
  $passed=$true
} catch {$failure=$_.Exception.Message;[Console]::Error.WriteLine($failure)}
finally {
  $spanFile=$OutputPath+'.function.ps1';[IO.File]::WriteAllBytes($spanFile,$spanBytes)
  $receipt=[ordered]@{passed=$passed;error=$failure;sourcePath=$SourcePath;sourceSha256=$ExpectedSourceSha256;sourceBytes=$sourceBytes.Length;
    spanStartByte=$start;spanBytes=$spanBytes.Length;spanSha256=(Get-FileHash -LiteralPath $spanFile).Hash.ToLowerInvariant();spanPath=$spanFile;
    vectorsSha256=$vectorHash;selected=$expectedIds;results=@($results.ToArray());unequalPairs=$vector.unequalPairs;
    shell=(Get-Process -Id $PID).Path;shellSha256=(Get-FileHash -LiteralPath (Get-Process -Id $PID).Path).Hash;
    version=$PSVersionTable.PSVersion.ToString();edition=$PSVersionTable.PSEdition;dotnet=[Environment]::Version.ToString();
    harnessSha256=(Get-FileHash -LiteralPath $PSCommandPath).Hash;scope='Exact source-derived Hash-Bytes component; full callers and file-pin finalizer are separate required checks'}
  [IO.File]::WriteAllText($OutputPath,($receipt|ConvertTo-Json -Depth 30),$utf8)
}
if(-not $passed){exit 7}
Write-Output 'L1R2-HASH PASS vectors=8 distinctions=3'
exit 0
