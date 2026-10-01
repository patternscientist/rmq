param([string]$OutputRoot,[string[]]$Kinds=@('focused','full','integrity','dependencies','checks','claims'),[string]$ExistingManifest)
$ErrorActionPreference='Stop'
# Validate the complete selection before creating output or invoking any profile.
if($PSBoundParameters.ContainsKey('Kinds')){
  if($null -eq $Kinds -or $Kinds.Count -eq 0 -or @($Kinds|Where-Object {[string]::IsNullOrWhiteSpace($_)}).Count){throw 'CERTIFY-SELECTOR: empty'}
  $known=[Collections.Generic.HashSet[string]]::new([string[]]@('focused','full','integrity','dependencies','checks','claims'),[StringComparer]::Ordinal)
  $seen=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($kind in $Kinds){
    if(-not $known.Contains($kind)){throw 'CERTIFY-SELECTOR: unknown'}
    if(-not $seen.Add($kind)){throw 'CERTIFY-SELECTOR: duplicate'}
  }
}
$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../..'))
if(-not $OutputRoot){$OutputRoot=Join-Path $repo ('.lake/repair-r2/certification-'+[Guid]::NewGuid().ToString('N'))}
[void][IO.Directory]::CreateDirectory($OutputRoot)
$encoding=[Text.UTF8Encoding]::new($false,$true)
$manifest=if($ExistingManifest){[IO.File]::ReadAllText($ExistingManifest,$encoding)|ConvertFrom-Json -AsHashtable}else{@{profiles=@{}}}
$manifestPath=Join-Path $OutputRoot 'PROFILES.json'
$shell=(Get-Process -Id $PID).Path
foreach($kind in $Kinds){
  $out=Join-Path $OutputRoot $kind
  if(Test-Path -LiteralPath $out){throw 'certification profile output must be fresh'}
  & $shell -NoProfile -File (Join-Path $PSScriptRoot '../repair-r1/run_owned.ps1') -Kind $kind -OutputRoot $out
  $actualExit=$LASTEXITCODE
  $receiptPath=Join-Path $out 'RECEIPT.json'
  $receipt=[IO.File]::ReadAllText($receiptPath,$encoding)|ConvertFrom-Json
  if($actualExit -ne 0 -or -not $receipt.streamValidation.validated){throw ('certification profile failed: '+$kind+'; '+$receipt.streamValidation.failure)}
  $manifest.profiles[$kind]=$receiptPath
  if($kind -ceq 'claims'){$manifest.claimExpectationPath=$receipt.claimExpectation.path}
  $manifest.head=(& git -C $repo rev-parse HEAD).Trim()
  [IO.File]::WriteAllText($manifestPath,($manifest|ConvertTo-Json -Depth 10),$encoding)
  Write-Output ('PROFILE CERTIFIED '+$kind+' manifest='+$manifestPath)
}
