$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
$repo = 'C:/Users/poin/.codex/worktrees/2270/RMQ'
$target = '5033ce54da233fc7a3df319d50ab09a2ebee523a'
$utf8 = [Text.UTF8Encoding]::new($false, $true)
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
$outputRoot = Join-Path $repo ('.lake/lb1-conflict-controls/' + [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff'))
[void][IO.Directory]::CreateDirectory($outputRoot)
$git = Resolve-RMQScalarApplicationPath (Get-Command git -CommandType Application) 'git'
$head = @(Invoke-RMQCheckedGit $git $repo @('rev-parse','HEAD') 'conflicts-head' 30 1048576 $outputRoot)[0]
if($head -cne $target) {throw 'Conflict-control source target changed'}
$state = Get-RMQRepositoryStateBounded -RepositoryRoot $repo -GitPath $git -DeadlineSeconds 30 -OutputLimitBytes 1048576 -TempRoot $outputRoot -StagePrefix 'conflicts-baseline'
Assert-RMQCleanRepositoryStateText $state 'conflicts-baseline'
$sourcePaths = @('RMQ/Core/EncodingVariableLowerBound.lean','RMQ/Core/WordRAM/Packed/AllocationLowerBound.lean','RMQ/Validation/VariablePayloadLowerBound.lean','scripts/variable_payload_replay.ps1','scripts/owned_process_tree.ps1','docs/internal/extensions/lb1/REPLAY_REGISTRY.json','lean-toolchain','lakefile.toml')
$hashes = @($sourcePaths | ForEach-Object {[pscustomobject]@{Path=$_;SHA256=(Get-FileHash -LiteralPath (Join-Path $repo $_)).Hash}})
$shell = (Get-Process -Id $PID).Path
$cases = @(
 [pscustomobject]@{ID='REPLAY-CLI-ENV-CONFLICT';File=$shell;Arguments=@('-NoProfile','-File',(Join-Path $repo 'scripts/variable_payload_replay.ps1'),'-OnlyCase','A01-BASELINE','-SelectorProbeOnly');Environment=@{LB1_REPLAY_SELECTOR='id:A01-BASELINE'};Diagnostic='LB1-SELECTOR supplied twice';Forbidden='LB1-SELECTOR-PASS|LB1-REPLAY CASE.*PASS|LB1-REPLAY-PASS';Deadline=180},
 [pscustomobject]@{ID='RUNTIME-CLI-ENV-CONFLICT';File='C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe';Arguments=@('-j1','--run',(Join-Path $repo 'RMQ/Validation/VariablePayloadLowerBound.lean'),'--case','R04-ZERO-LENGTH');Environment=@{LB1_RUNTIME_SELECTOR='case:R04-ZERO-LENGTH';LEAN_PATH=(Join-Path $repo '.lake/build/lib/lean')};Diagnostic='LB1-RUNTIME selector supplied twice';Forbidden='LB1-RUNTIME CASE PASS|LB1-RUNTIME PASS';Deadline=600},
 [pscustomobject]@{ID='RUNTIME-MALFORMED-ID';File='C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe';Arguments=@('-j1','--run',(Join-Path $repo 'RMQ/Validation/VariablePayloadLowerBound.lean'));Environment=@{LB1_RUNTIME_SELECTOR='case:not an id';LEAN_PATH=(Join-Path $repo '.lake/build/lib/lean')};Diagnostic='LB1-RUNTIME malformed selector';Forbidden='LB1-RUNTIME CASE PASS|LB1-RUNTIME PASS|malformed selector channel';Deadline=600})
$records = @()
foreach($case in $cases) {
 Write-Host ('LB1-CONFLICT START '+$case.ID)
 $result = Invoke-RMQOwnedBoundedProcess -FilePath $case.File -Arguments $case.Arguments -WorkingDirectory $repo -Stage $case.ID -DeadlineSeconds $case.Deadline -OutputLimitBytes 4194304 -TempRoot $outputRoot -Environment $case.Environment
 $record = [ordered]@{UTC=[DateTime]::UtcNow.ToString('o');Commit=$head;Case=$case.ID;Command=@($case.File)+$case.Arguments;Environment=$case.Environment;WorkingDirectory=$repo;Sources=$hashes;Result=$result;ExpectedDiagnostic=$case.Diagnostic;ExpectedVerdict='REJECT before any case pass'}
 [IO.File]::WriteAllText((Join-Path $outputRoot ($case.ID+'.json')),($record|ConvertTo-Json -Depth 10),$utf8)
 $records += $record
 $output = $result.Output -join "`n"
 if($result.TimedOut -or $result.OutputLimitExceeded -or $result.ExitCode -eq 0) {throw ('Conflict probe failed or inconclusive: '+$case.ID)}
 if(-not $output.Contains($case.Diagnostic) -or $output -match $case.Forbidden -or $output -match 'maximum recursion|maximum heartbeats|unknown module prefix|object file.*does not exist') {throw ('Conflict probe wrong surface: '+$case.ID)}
 Write-Host ('LB1-CONFLICT PASS '+$case.ID+' seconds='+$result.DurationSeconds)
}
foreach($source in $hashes) {if((Get-FileHash -LiteralPath (Join-Path $repo $source.Path)).Hash -cne $source.SHA256) {throw ('Source changed '+$source.Path)}}
$state = Get-RMQRepositoryStateBounded -RepositoryRoot $repo -GitPath $git -DeadlineSeconds 30 -OutputLimitBytes 1048576 -TempRoot $outputRoot -StagePrefix 'conflicts-final'
Assert-RMQCleanRepositoryStateText $state 'conflicts-final'
$summary = [ordered]@{Commit=$head;Expected=@($cases.ID);Executed=@($cases.ID);Records=$records;SourceUnchanged=$true;CleanTree=$true;Scope='Two externally supplied simultaneous CLI/environment selectors, plus malformed runtime ID inside a valid case: channel; distinct parsing branches are checked explicitly.'}
[IO.File]::WriteAllText((Join-Path $outputRoot 'summary.json'),($summary|ConvertTo-Json -Depth 12),$utf8)
Write-Host ('LB1-CONFLICT COMPLETE evidence='+$outputRoot)
