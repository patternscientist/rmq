#!/usr/bin/env pwsh
[CmdletBinding()]
param([ValidateRange(10,300)][int]$DeadlineSeconds=60)
$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$utf8=[Text.UTF8Encoding]::new($false,$true)
$freeze='0bbbe8ca4a937bc9782b2f7c5cc5419faa1a75a2'
$matrix='docs/internal/extensions/lb1/ACCEPTANCE_MATRIX.md'
$expectedIDs=@(
  'REQ-LB-COUNT','REQ-LB-PQ1','REQ-LB-MODEL','REQ-LB-CONSUMER','CHK-LB-CONTROLS',
  'REPLAY-EXACT-REGISTRY','REPLAY-SELECTOR-NONVACUITY','REPLAY-SUBPROCESS-DEADLINE',
  'INV-STORE-IDENTITY','INV-VALUE-DEPENDENCY','INV-SEMANTIC-NONVACUITY',
  'INV-TRACE-EXECUTION','INV-STORE-AGREEMENT','INV-READ-BACKING','INV-WORD-WIDTH',
  'INV-ADDRESS-WIDTH','INV-INSTRUCTION-ATOMICITY','INV-PROGRAM-ACCOUNTING',
  'INV-ORACLE-INDEPENDENCE','INV-VALIDATION-REACH','INV-ALL-SIZE',
  'INV-PROOF-SEPARATION','INV-NO-SYNTHETIC','INV-CATEGORY-SEPARATION',
  'INV-PUBLIC-COMPOSITION','INV-CERTIFICATE-ANTI-BYPASS',
  'INV-MUTATION-REPRODUCIBILITY','INV-GLOBAL-PHYSICAL-MACHINE','INV-WIDTH-SCALING'
)
$controlRegistry=@(
  'F01-UNCHANGED|ACCEPT|OK',
  'F02-ROW-WHITESPACE|REJECT|ROW_BYTES_DIFFER',
  'F03-MISSING-ROW|REJECT|MISSING_ROW',
  'F04-DUPLICATE-ROW|REJECT|DUPLICATE_ROW',
  'F05-UNICODE-CORRUPTION|REJECT|ROW_BYTES_DIFFER',
  'F06-MOJIBAKE|REJECT|MOJIBAKE',
  'F07-INVALID-UTF8|REJECT|INVALID_UTF8'
)
if($expectedIDs.Count -ne 29 -or @($expectedIDs|Select-Object -Unique).Count -ne 29 -or
    $controlRegistry.Count -ne 7){throw 'LB1-FROZEN literal registry count changed'}

function Get-LB1SHA256([byte[]]$bytes){
  $sha=[Security.Cryptography.SHA256]::Create()
  try{return [Convert]::ToHexString($sha.ComputeHash($bytes))}finally{$sha.Dispose()}
}
function Copy-LB1ByteSlice([byte[]]$bytes,[int]$start,[int]$count){
  $slice=[byte[]]::new($count)
  [Array]::Copy($bytes,$start,$slice,0,$count)
  return ,$slice
}
function Replace-LB1ByteRange([byte[]]$bytes,[int]$start,[int]$count,[byte[]]$replacement){
  $result=[byte[]]::new($bytes.Length-$count+$replacement.Length)
  [Array]::Copy($bytes,0,$result,0,$start)
  [Array]::Copy($replacement,0,$result,$start,$replacement.Length)
  [Array]::Copy($bytes,$start+$count,$result,$start+$replacement.Length,$bytes.Length-$start-$count)
  return ,$result
}
function Get-LB1FrozenRows([byte[]]$bytes){
  try{$decoded=$utf8.GetString($bytes)}catch [Text.DecoderFallbackException]{
    throw 'LB1-FROZEN:INVALID_UTF8:document'
  }
  # Recognizable mojibake is an additional negative check, never a substitute
  # for exact row bytes. Character codes keep this script's own text unambiguous.
  $needles=@(
    (([string][char]0x00C2)+[char]0x00AC),
    (([string][char]0x00E2)+[char]0x20AC),
    (([string][char]0x00C3)+[char]0x00A9),
    ([string][char]0xFFFD)
  )
  foreach($needle in $needles){
    if($decoded.Contains($needle,[StringComparison]::Ordinal)){throw 'LB1-FROZEN:MOJIBAKE:document'}
  }
  $rows=[Collections.Generic.Dictionary[string,object]]::new([StringComparer]::Ordinal)
  # A row is the entire physical line starting "| ID |" at column one.
  # LF and CRLF are delimiters, not row content. Only a CR immediately before
  # an actual LF is excluded. Every other byte, including leading/trailing
  # whitespace, remains content; no whitespace or Unicode normalization occurs.
  $start=0
  for($position=0;$position -le $bytes.Length;$position++){
    if($position -lt $bytes.Length -and $bytes[$position] -ne 10){continue}
    $hasLF=$position -lt $bytes.Length
    $end=$position
    if($hasLF -and $end -gt $start -and $bytes[$end-1] -eq 13){$end--}
    $count=$end-$start
    $line=$utf8.GetString($bytes,$start,$count)
    $match=[regex]::Match($line,'^\| (?<id>(?:REQ-LB-|CHK-LB-|REPLAY-|INV-)[A-Z0-9-]+) \|')
    if($match.Success){
      $id=$match.Groups['id'].Value
      if($expectedIDs -cnotcontains $id){throw "LB1-FROZEN:UNEXPECTED_ROW:$id"}
      if($rows.ContainsKey($id)){throw "LB1-FROZEN:DUPLICATE_ROW:$id"}
      $rowBytes=Copy-LB1ByteSlice $bytes $start $count
      $rows.Add($id,[pscustomobject]@{ID=$id;Start=$start;Count=$count;
        DelimitedCount=($position-$start+[int]$hasLF);Bytes=$rowBytes;Text=$line})
    }
    $start=$position+1
  }
  foreach($id in $expectedIDs){if(-not $rows.ContainsKey($id)){throw "LB1-FROZEN:MISSING_ROW:$id"}}
  return ,$rows
}
function Test-LB1FrozenRows([byte[]]$frozen,[byte[]]$candidate){
  try{
    $baseRows=Get-LB1FrozenRows $frozen
    $candidateRows=Get-LB1FrozenRows $candidate
  }catch{
    if($_.Exception.Message -notmatch '^LB1-FROZEN:([A-Z0-9_]+):(.+)$'){throw}
    return [pscustomobject]@{Accepted=$false;Code=$Matches[1];ChangedIDs=@($Matches[2]);Rows=@()}
  }
  $changed=@($expectedIDs|Where-Object{
    [Convert]::ToBase64String($baseRows[$_].Bytes) -cne
      [Convert]::ToBase64String($candidateRows[$_].Bytes)
  })
  $evidence=@(foreach($id in $expectedIDs){[pscustomobject]@{
    ID=$id;BaseBytes=$baseRows[$id].Count;CandidateBytes=$candidateRows[$id].Count;
    BaseSHA256=(Get-LB1SHA256 $baseRows[$id].Bytes);
    CandidateSHA256=(Get-LB1SHA256 $candidateRows[$id].Bytes)
  }})
  return [pscustomobject]@{Accepted=($changed.Count -eq 0);
    Code=$(if($changed.Count -eq 0){'OK'}else{'ROW_BYTES_DIFFER'});ChangedIDs=$changed;Rows=$evidence}
}

$runRoot=Join-Path $repo ('.lake/lb1-contract-check/'+[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff'))
[void][IO.Directory]::CreateDirectory($runRoot)
$git=Resolve-RMQScalarApplicationPath (Get-Command git -CommandType Application) 'git'
$blobSpec=$freeze+':'+$matrix
$blobPath=Join-Path $runRoot 'frozen-matrix.bin'
$launchPath=Join-Path $runRoot 'binary-git.json'
$helperPath=Join-Path $runRoot 'binary-git.ps1'
[IO.File]::WriteAllText($launchPath,([ordered]@{Git=$git;Repository=$repo;Blob=$blobSpec;Output=$blobPath}|ConvertTo-Json),$utf8)
# This helper copies raw stdout bytes. Neither PowerShell's native text pipeline
# nor the owned wrapper's decoded Output is used to retrieve the Git blob.
$helper=@'
param([string]$SpecPath)
$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
$spec=[IO.File]::ReadAllText($SpecPath,[Text.UTF8Encoding]::new($false,$true))|ConvertFrom-Json
if($spec.Blob -cnotmatch '^[0-9a-f]{40}:docs/internal/extensions/lb1/ACCEPTANCE_MATRIX\.md$'){throw 'Unexpected fixed blob spec'}
$start=[Diagnostics.ProcessStartInfo]::new()
$start.FileName=[string]$spec.Git
$start.Arguments='cat-file blob '+[string]$spec.Blob
$start.WorkingDirectory=[string]$spec.Repository
$start.UseShellExecute=$false
$start.CreateNoWindow=$true
$start.RedirectStandardOutput=$true
$start.RedirectStandardError=$true
$process=[Diagnostics.Process]::new()
$process.StartInfo=$start
$output=$null
try{
  if(-not $process.Start()){throw 'Could not start owned Git child'}
  $stderr=$process.StandardError.ReadToEndAsync()
  $output=[IO.File]::Open([string]$spec.Output,[IO.FileMode]::CreateNew,[IO.FileAccess]::Write,[IO.FileShare]::None)
  $buffer=[byte[]]::new(8192)
  $total=0
  while(($count=$process.StandardOutput.BaseStream.Read($buffer,0,$buffer.Length)) -gt 0){
    $total+=$count
    if($total -gt 4194304){throw 'Frozen blob exceeds bounded retrieval size'}
    $output.Write($buffer,0,$count)
  }
  $output.Flush()
  $process.WaitForExit()
  [Console]::Error.Write($stderr.GetAwaiter().GetResult())
  $code=$process.ExitCode
  Write-Output "LB1-FROZEN binary Git bytes=$total exit=$code"
  exit $code
}finally{if($null -ne $output){$output.Dispose()};$process.Dispose()}
'@
[IO.File]::WriteAllText($helperPath,$helper,$utf8)
$shell=(Get-Process -Id $PID).Path
$retrieval=Invoke-RMQOwnedBoundedProcess -FilePath $shell -Arguments @('-NoProfile','-File',$helperPath,'-SpecPath',$launchPath) -WorkingDirectory $repo -Stage 'lb1-frozen-binary-git' -DeadlineSeconds $DeadlineSeconds -OutputLimitBytes 1048576 -TempRoot $runRoot
[IO.File]::WriteAllText((Join-Path $runRoot 'binary-git-result.json'),($retrieval|ConvertTo-Json -Depth 9),$utf8)
if($retrieval.TimedOut -or $retrieval.OutputLimitExceeded -or $retrieval.ExitCode -ne 0){
  throw "LB1-FROZEN retrieval incomplete: $($retrieval.Output -join ' | ')"
}
$blobOID=@(Invoke-RMQCheckedGit $git $repo @('rev-parse',$blobSpec) 'lb1-frozen-blob-id' $DeadlineSeconds 1048576 $runRoot)
$candidateHEAD=@(Invoke-RMQCheckedGit $git $repo @('rev-parse','HEAD') 'lb1-frozen-candidate-head' $DeadlineSeconds 1048576 $runRoot)
if($blobOID.Count -ne 1 -or $blobOID[0] -cnotmatch '^[0-9a-f]{40}$' -or
    $candidateHEAD.Count -ne 1 -or $candidateHEAD[0] -cnotmatch '^[0-9a-f]{40}$'){throw 'LB1-FROZEN invalid Git identity'}
$frozenBytes=[IO.File]::ReadAllBytes($blobPath)
$candidatePath=Join-Path $repo $matrix
$candidateBytes=[IO.File]::ReadAllBytes($candidatePath)
$comparison=Test-LB1FrozenRows $frozenBytes $candidateBytes
if(-not $comparison.Accepted){throw "LB1-FROZEN candidate rejected: $($comparison.Code) $($comparison.ChangedIDs -join ',')"}

$baseRows=Get-LB1FrozenRows $frozenBytes
$target=$baseRows['REQ-LB-COUNT']
$completeRow=Copy-LB1ByteSlice $frozenBytes $target.Start $target.DelimitedCount
$mutations=@{}
$mutations['F01-UNCHANGED']=$frozenBytes
$mutations['F02-ROW-WHITESPACE']=Replace-LB1ByteRange $frozenBytes $target.Start $target.Count ([byte[]]($target.Bytes+@(32)))
$mutations['F03-MISSING-ROW']=Replace-LB1ByteRange $frozenBytes $target.Start $target.DelimitedCount ([byte[]]@())
$mutations['F04-DUPLICATE-ROW']=Replace-LB1ByteRange $frozenBytes $target.Start $target.DelimitedCount ([byte[]]($completeRow+$completeRow))
$mutations['F05-UNICODE-CORRUPTION']=Replace-LB1ByteRange $frozenBytes $target.Start $target.Count ([byte[]]($target.Bytes+$utf8.GetBytes([string][char]0x0394)))
$mutations['F06-MOJIBAKE']=Replace-LB1ByteRange $frozenBytes $target.Start $target.Count ([byte[]]($target.Bytes+$utf8.GetBytes(([string][char]0x00C2)+[char]0x00AC)))
$mutations['F07-INVALID-UTF8']=[byte[]]($frozenBytes+@(255))
$controls=[Collections.Generic.List[object]]::new()
foreach($entry in $controlRegistry){
  $parts=$entry.Split('|')
  $id=$parts[0]
  $result=Test-LB1FrozenRows $frozenBytes $mutations[$id]
  $verdict=if($result.Accepted){'ACCEPT'}else{'REJECT'}
  if($verdict -cne $parts[1] -or $result.Code -cne $parts[2]){throw "LB1-FROZEN control verdict mismatch: $id $verdict $($result.Code)"}
  if($id -in @('F02-ROW-WHITESPACE','F03-MISSING-ROW','F04-DUPLICATE-ROW','F05-UNICODE-CORRUPTION') -and
      ($result.ChangedIDs -join ',') -cne 'REQ-LB-COUNT'){throw "LB1-FROZEN wrong affected row: $id"}
  $controls.Add([pscustomobject]@{ID=$id;Expected=$parts[1];Actual=$verdict;Code=$result.Code;ChangedIDs=$result.ChangedIDs})
}
$executed=@($controls|ForEach-Object{$_.ID})
$expectedControls=@($controlRegistry|ForEach-Object{$_.Split('|')[0]})
if(($executed -join '|') -cne ($expectedControls -join '|')){throw 'LB1-FROZEN exact control registry not executed'}
if([Convert]::ToBase64String([IO.File]::ReadAllBytes($candidatePath)) -cne [Convert]::ToBase64String($candidateBytes)){
  throw 'LB1-FROZEN candidate changed concurrently; do not reuse this result'
}
$evidence=[ordered]@{
  Version=1;FreezeCommit=$freeze;BlobSpec=$blobSpec;BlobOID=$blobOID[0];CandidateHEAD=$candidateHEAD[0];
  Candidate='working-file snapshot';Matrix=$matrix;BaseFileBytes=$frozenBytes.Length;
  CandidateFileBytes=$candidateBytes.Length;BaseFileSHA256=(Get-LB1SHA256 $frozenBytes);
  CandidateFileSHA256=(Get-LB1SHA256 $candidateBytes);CheckerSHA256=(Get-FileHash -LiteralPath $PSCommandPath -Algorithm SHA256).Hash;
  StrictUTF8=$true;RowDelimiter='LF or CRLF excluded; every other physical-row byte preserved';
  ExpectedIDs=$expectedIDs;RowCount=$comparison.Rows.Count;ChangedIDs=$comparison.ChangedIDs;
  Rows=$comparison.Rows;ControlRegistryVersion=1;ExpectedControls=$expectedControls;ExecutedControls=$executed;
  Controls=$controls;CandidateBytesUnchanged=$true;SourceMutations='in-memory only';BinaryGitRetrieval=$retrieval
}
$evidencePath=Join-Path $runRoot 'evidence.json'
[IO.File]::WriteAllText($evidencePath,($evidence|ConvertTo-Json -Depth 12),$utf8)
Write-Host "LB1-FROZEN-PASS rows=29 changed=0 controls_expected=7 controls_executed=7 evidence=$evidencePath"
