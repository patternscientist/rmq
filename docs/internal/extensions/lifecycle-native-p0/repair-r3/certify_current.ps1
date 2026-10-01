param([Parameter(Mandatory)][string]$OutputRoot,[Parameter(Mandatory)][string]$FocusedManifest,[Parameter(Mandatory)][string]$HistoricalContract)
$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../..'))
$utf8=[Text.UTF8Encoding]::new($false,$true)
$base='9519b2c1af5e2cf59536b311db5e8dc81376a32f'
$OutputRoot=[IO.Path]::GetFullPath($OutputRoot);$FocusedManifest=[IO.Path]::GetFullPath($FocusedManifest);$HistoricalContract=[IO.Path]::GetFullPath($HistoricalContract)
$allowed=[IO.Path]::GetFullPath((Join-Path $repo '.lake/repair-r3')).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
if(-not $OutputRoot.StartsWith($allowed,[StringComparison]::OrdinalIgnoreCase) -or (Test-Path -LiteralPath $OutputRoot)){throw 'fresh owned final output required'}
[void][IO.Directory]::CreateDirectory($OutputRoot)
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
. (Join-Path $repo 'scripts/packed_native_lifecycle_integrity_check.ps1')
$before=$null;$after=$null;$scanBefore=$null;$scanAfter=$null;$head=$null;$failure=$null;$initialStatus=$null;$finalStatus=$null
$sourcePins=@();$focusedPin=$null;$historyPin=$null;$seedPin=$null;$profilesPin=$null
$errors=[Collections.Generic.List[string]]::new()
$selector=Join-Path $PSScriptRoot '../repair-r2/certify_profiles.ps1'
$profiles=Join-Path $OutputRoot 'profiles/PROFILES.json'
function Scan-Inputs {
  $paths=@(Get-ChildItem -LiteralPath (Join-Path $repo 'docs/internal/extensions/lifecycle-native-p0') -Recurse -File -Force|ForEach-Object {$_.FullName})
  $paths+=@((Join-Path $repo 'docs/internal/DESIGN_DECISIONS.md'),(Join-Path $repo 'docs/internal/WORKFLOW_DESIGN_DECISIONS.md'))
  @($paths|Sort-Object|ForEach-Object {Get-LNRawPin $_})
}
function Same($a,$b,[string]$name){if(-not [string]::Equals(($a|ConvertTo-Json -Depth 15 -Compress),($b|ConvertTo-Json -Depth 15 -Compress),[StringComparison]::Ordinal)){throw ($name+' changed')}}
try {
  $before=Get-LNTreeSnapshot $repo (Join-Path $OutputRoot 'before');$head=$before.head
  $initialStatus=@(& git -C $repo -c core.excludesfile= status --porcelain=v1 --untracked-files=all)
  if($LASTEXITCODE -ne 0 -or $initialStatus.Count){throw 'initial final candidate is not clean'}
  $scanBefore=@(Scan-Inputs)
  $sourcePaths=@($PSCommandPath,$selector,(Join-Path $PSScriptRoot '../repair-r1/run_owned.ps1'),(Join-Path $PSScriptRoot '../repair-r1/final_checks.ps1'),(Join-Path $PSScriptRoot '../repair-r2/claim_expectations.ps1'),(Join-Path $repo 'scripts/owned_process_tree.ps1'),(Join-Path $repo 'scripts/packed_native_lifecycle_stream_check.ps1'),(Join-Path $repo 'scripts/packed_native_lifecycle_integrity_check.ps1'))
  $sourcePins=@($sourcePaths|ForEach-Object {Get-LNRawPin $_});$focusedPin=Get-LNRawPin $FocusedManifest;$historyPin=Get-LNRawPin $HistoricalContract
  $focused=[IO.File]::ReadAllText($FocusedManifest,$utf8)|ConvertFrom-Json -AsHashtable
  $history=[IO.File]::ReadAllText($HistoricalContract,$utf8)|ConvertFrom-Json -AsHashtable
  if($focused.profiles.Count -ne 1 -or -not $focused.profiles.ContainsKey('focused')){throw 'focused manifest must contain exactly focused'}
  if(-not $history.success -or $history.mode -cne 'full-contract' -or $history.base -cne $base -or $history.historicalR2.packageCommit -cne $base -or [IO.Path]::GetFullPath($history.worktree) -cne $repo){throw 'historical preservation contract identity differs'}
  $seed=@{head=$head;profiles=@{focused=$focused.profiles.focused}}
  foreach($kind in @('full','integrity','dependencies')){$seed.profiles[$kind]=$history.historicalR2.profiles[$kind].receipt.path}
  $seedPath=Join-Path $OutputRoot 'SEED.json';[IO.File]::WriteAllText($seedPath,($seed|ConvertTo-Json -Depth 12),$utf8);$seedPin=Get-LNRawPin $seedPath
  & $selector -Kinds @('checks','claims') -ExistingManifest $seedPath -OutputRoot (Join-Path $OutputRoot 'profiles')
  if($LASTEXITCODE -ne 0){throw 'current certification did not return ordinary zero'}
  $manifest=[IO.File]::ReadAllText($profiles,$utf8)|ConvertFrom-Json -AsHashtable
  if($manifest.head -cne $head -or $manifest.profiles.Count -ne 6){throw 'final six-profile manifest identity differs'}
  foreach($kind in @('focused','full','integrity','dependencies','checks','claims')){if(-not $manifest.profiles.ContainsKey($kind)){throw 'final profile missing'}}
}catch{$failure=$_.Exception.Message}
finally {
  foreach($pin in @(@($sourcePins)+@($focusedPin,$historyPin,$seedPin)|Where-Object {$null -ne $_})){
    try{Same (Get-LNRawPin $pin.path) $pin 'final captured source/input pin'}catch{$errors.Add($_.Exception.Message)}
  }
  try{if($null -eq $before){throw 'initial final snapshot unavailable'};$after=Get-LNTreeSnapshot $repo (Join-Path $OutputRoot 'after');Same $after $before 'final tracked/index/untracked tree'}catch{$errors.Add($_.Exception.Message)}
  try{if($null -eq $scanBefore){throw 'initial scan input inventory unavailable'};$scanAfter=@(Scan-Inputs);Same $scanAfter $scanBefore 'entire subtree/both-ledger input bytes'}catch{$errors.Add($_.Exception.Message)}
  try{$finalStatus=@(& git -C $repo -c core.excludesfile= status --porcelain=v1 --untracked-files=all);if($LASTEXITCODE -ne 0 -or $finalStatus.Count){throw 'final candidate is not clean'}}catch{$errors.Add($_.Exception.Message)}
  try{if([IO.File]::Exists($profiles)){$profilesPin=Get-LNRawPin $profiles}}catch{$errors.Add($_.Exception.Message)}
  $result=[ordered]@{success=($null -eq $failure -and $errors.Count -eq 0);base=$base;head=$head;worktree=$repo;before=$before;after=$after;initialStatus=$initialStatus;finalStatus=$finalStatus;
    scanInputsBefore=$scanBefore;scanInputsAfter=$scanAfter;sourcePins=$sourcePins;focusedManifest=$focusedPin;historicalContract=$historyPin;seed=$seedPin;profiles=$profilesPin;failure=$failure;
    finalIntegrity=@{attempted=$true;success=($errors.Count -eq 0);errors=@($errors.ToArray())}}
  [IO.File]::WriteAllText((Join-Path $OutputRoot 'RESULTS.json'),($result|ConvertTo-Json -Depth 35),$utf8)
}
if(-not $result.success){throw ('current profile certification failed: '+$failure+'; integrity='+($errors -join '; '))}
Write-Output ('CURRENT PROFILES PASS evidence='+$OutputRoot)
