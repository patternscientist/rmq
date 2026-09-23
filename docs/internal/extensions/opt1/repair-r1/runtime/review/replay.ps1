[CmdletBinding()]
param()
$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
$repoRoot=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../../../..'))
$target=Join-Path $repoRoot 'scripts/packed_optimized_replay_regression.ps1'
$tokens=$null; $errors=$null
$ast=[Management.Automation.Language.Parser]::ParseFile($target,[ref]$tokens,[ref]$errors)
if(@($errors).Count -ne 0){throw 'Parent regression parse failed'}
$definitions=@($ast.FindAll({param($node) $node -is [Management.Automation.Language.FunctionDefinitionAst] -and $node.Name -ceq 'Assert-R1Verdict'},$true))
if($definitions.Count -ne 1){throw 'Actual verdict function missing/duplicate'}
. ([scriptblock]::Create($definitions[0].Extent.Text))
. (Join-Path $repoRoot 'scripts/owned_process_tree.ps1')
$outputRoot=Join-Path $repoRoot ('.lake/opt1-r1-runtime/parent-verdict-review-'+[Guid]::NewGuid().ToString('N'))
[void][IO.Directory]::CreateDirectory($outputRoot)
$utf8=[Text.UTF8Encoding]::new($false,$true)
$shell=(Get-Process -Id $PID).Path
$records=@()
foreach($mode in @('sole-expected','mixed-unrelated-stdout','mixed-success-stdout')){
 $child=Join-Path $outputRoot ($mode+'.ps1')
 $text="[Console]::Error.WriteLine('OPT1-CERT-IMPORT: source/artifact differs from checked provenance: RMQ/Core/Backend.lean')`n"
 if($mode -ceq 'mixed-unrelated-stdout'){$text+="[Console]::Out.WriteLine('uncaught exception: independent parent-review failure')`n"}
 if($mode -ceq 'mixed-success-stdout'){$text+="[Console]::Out.WriteLine('OPT1-CERT-REPLAY PASS executed=80 expected=80 registry=opt1-certificate-replay-v3')`n"}
 $text+="exit 1`n"
 [IO.File]::WriteAllText($child,$text,$utf8)
 $result=Invoke-RMQOwnedBoundedProcess -FilePath $shell -Arguments @('-NoProfile','-File',$child) -WorkingDirectory $repoRoot -Stage $mode -DeadlineSeconds 60 -OutputLimitBytes 1048576 -TempRoot $outputRoot
 if($result.TimedOut -or $result.OutputLimitExceeded -or $result.ExitCode -ne 1){throw 'Review fixture setup failed'}
 $accepted=$true; $diagnostic=''
 try{Assert-R1Verdict $result 1 'OPT1-CERT-IMPORT:'}catch{$accepted=$false;$diagnostic=$_.Exception.Message}
 $records += @{Mode=$mode;Accepted=$accepted;Diagnostic=$diagnostic;ActualResult=$result}
}
$receipt=@{ParentRunnerSHA256=(Get-FileHash -LiteralPath $target).Hash;ActualFunction='Assert-R1Verdict';Cases=$records;Meaning='Read-only review of parent regression acceptance, not Lean semantic replay'}
[IO.File]::WriteAllText((Join-Path $outputRoot 'RESULT.json'),($receipt|ConvertTo-Json -Depth 20),$utf8)
Write-Host "PARENT-VERDICT REVIEW $outputRoot"
$records|Select-Object Mode,Accepted|ConvertTo-Json
