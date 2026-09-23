$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
$repo = 'C:/Users/poin/.codex/worktrees/2270/RMQ'
$target = '5033ce54da233fc7a3df319d50ab09a2ebee523a'
$utf8 = [Text.UTF8Encoding]::new($false, $true)
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
$outputRoot = Join-Path $repo ('.lake/lb1-focused/' + [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff'))
[void][IO.Directory]::CreateDirectory($outputRoot)
$git = Resolve-RMQScalarApplicationPath (Get-Command git -CommandType Application) 'git'
$shell = (Get-Process -Id $PID).Path
$head = @(Invoke-RMQCheckedGit $git $repo @('rev-parse','HEAD') 'focused-head' 30 1048576 $outputRoot)[0]
if ($head -cne $target) { throw 'Focused verification target changed' }
$state = Get-RMQRepositoryStateBounded -RepositoryRoot $repo -GitPath $git -DeadlineSeconds 30 -OutputLimitBytes 1048576 -TempRoot $outputRoot -StagePrefix 'focused-baseline'
Assert-RMQCleanRepositoryStateText $state 'focused-baseline'
$sourcePaths = @(
  'RMQ/Core/EncodingVariableLowerBound.lean',
  'RMQ/Core/WordRAM/Packed/AllocationLowerBound.lean',
  'RMQ/Validation/VariablePayloadLowerBound.lean',
  'scripts/variable_payload_replay.ps1',
  'scripts/variable_payload_inventory.lean',
  'scripts/variable_payload_generic_consumer.lean',
  'scripts/owned_process_tree.ps1',
  'docs/internal/extensions/lb1/REPLAY_REGISTRY.json',
  'lean-toolchain','lakefile.toml')
$hashes = @($sourcePaths | ForEach-Object {
  [pscustomobject]@{Path=$_;SHA256=(Get-FileHash -LiteralPath (Join-Path $repo $_) -Algorithm SHA256).Hash}
})
$records = [Collections.Generic.List[object]]::new()
$modes = @(
  [pscustomobject]@{Name='RegistryOnly';Deadline=180},
  [pscustomobject]@{Name='SelectorBoundaryOnly';Deadline=600},
  [pscustomobject]@{Name='DiagnosticOnly';Deadline=180},
  [pscustomobject]@{Name='DeadlineOnly';Deadline=180},
  [pscustomobject]@{Name='RuntimeOnly';Deadline=1200})
foreach ($mode in $modes) {
  $arguments = @('-NoProfile','-File',(Join-Path $repo 'scripts/variable_payload_replay.ps1'),('-'+$mode.Name),'-DeadlineSeconds','600','-LeanPath','C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe')
  Write-Host ('LB1-FOCUSED START ' + $mode.Name)
  $rootsBefore = @(Get-ChildItem -LiteralPath (Join-Path $repo '.lake/lb1-replay') -Directory | ForEach-Object {$_.FullName})
  $result = Invoke-RMQOwnedBoundedProcess -FilePath $shell -Arguments $arguments -WorkingDirectory $repo -Stage ('focused-'+$mode.Name) -DeadlineSeconds $mode.Deadline -OutputLimitBytes 8388608 -TempRoot $outputRoot
  $newRoots = @(Get-ChildItem -LiteralPath (Join-Path $repo '.lake/lb1-replay') -Directory | Where-Object {$_.FullName -cnotin $rootsBefore} | ForEach-Object {$_.FullName})
  $record = [ordered]@{UTC=[DateTime]::UtcNow.ToString('o');Commit=$head;Command=@($shell)+$arguments;WorkingDirectory=$repo;Sources=$hashes;CreatedReplayRoots=$newRoots;Result=$result}
  $records.Add($record)
  [IO.File]::WriteAllText((Join-Path $outputRoot ($mode.Name+'.json')),($record|ConvertTo-Json -Depth 10),$utf8)
  if ($result.TimedOut -or $result.OutputLimitExceeded -or $result.ExitCode -ne 0) {
    throw ('Focused mode failed or inconclusive: '+$mode.Name+'; evidence='+$outputRoot)
  }
  foreach ($source in $hashes) {
    if ((Get-FileHash -LiteralPath (Join-Path $repo $source.Path) -Algorithm SHA256).Hash -cne $source.SHA256) { throw ('Source changed: '+$source.Path) }
  }
  $state = Get-RMQRepositoryStateBounded -RepositoryRoot $repo -GitPath $git -DeadlineSeconds 30 -OutputLimitBytes 1048576 -TempRoot $outputRoot -StagePrefix ('focused-restored-'+$mode.Name)
  Assert-RMQCleanRepositoryStateText $state ('focused-restored-'+$mode.Name)
  Write-Host ('LB1-FOCUSED PASS '+$mode.Name+' seconds='+$result.DurationSeconds)
}
$summary = [ordered]@{Commit=$head;Expected=@($modes.Name);Executed=@($modes.Name);Records=@($records);SourceUnchanged=$true;CleanTree=$true;POSIX='UNOBSERVED on this Windows host';Reason='Close independent-audit focused-entry provenance gap on the exact candidate; semantic mutation registry is not repeated.'}
[IO.File]::WriteAllText((Join-Path $outputRoot 'summary.json'),($summary|ConvertTo-Json -Depth 13),$utf8)
Write-Host ('LB1-FOCUSED COMPLETE evidence='+$outputRoot)
