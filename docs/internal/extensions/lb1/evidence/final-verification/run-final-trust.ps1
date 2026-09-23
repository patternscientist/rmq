$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
$repo = 'C:/Users/poin/.codex/worktrees/2270/RMQ'
$target = '5033ce54da233fc7a3df319d50ab09a2ebee523a'
$utf8 = [Text.UTF8Encoding]::new($false, $true)
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
$outputRoot = Join-Path $repo ('.lake/lb1-final-trust/' + [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff'))
[void][IO.Directory]::CreateDirectory($outputRoot)
$git = Resolve-RMQScalarApplicationPath (Get-Command git -CommandType Application) 'git'
$head = @(Invoke-RMQCheckedGit $git $repo @('rev-parse','HEAD') 'trust-head' 30 1048576 $outputRoot)[0]
if ($head -cne $target) { throw 'Final trust target changed' }
$state = Get-RMQRepositoryStateBounded -RepositoryRoot $repo -GitPath $git -DeadlineSeconds 30 -OutputLimitBytes 1048576 -TempRoot $outputRoot -StagePrefix 'trust-baseline'
Assert-RMQCleanRepositoryStateText $state 'trust-baseline'
$sourcePaths = @('RMQ/Core/EncodingVariableLowerBound.lean','RMQ/Core/WordRAM/Packed/AllocationLowerBound.lean','RMQ/Validation/VariablePayloadLowerBound.lean','scripts/variable_payload_axioms.lean','scripts/owned_process_tree.ps1','lean-toolchain','lakefile.toml')
$hashes = @($sourcePaths | ForEach-Object { [pscustomobject]@{Path=$_;SHA256=(Get-FileHash -LiteralPath (Join-Path $repo $_) -Algorithm SHA256).Hash} })
$lean = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe'
$arguments = @('-j1','scripts/variable_payload_axioms.lean')
$result = Invoke-RMQOwnedBoundedProcess -FilePath $lean -Arguments $arguments -WorkingDirectory $repo -Stage 'lb1-final-axiom-inventory' -DeadlineSeconds 600 -OutputLimitBytes 4194304 -TempRoot $outputRoot -Environment @{LEAN_PATH=(Join-Path $repo '.lake/build/lib/lean')}
$record = [ordered]@{UTC=[DateTime]::UtcNow.ToString('o');Commit=$head;Command=@($lean)+$arguments;WorkingDirectory=$repo;Sources=$hashes;Result=$result;DeadlineReason='Prior comparable 20-name inventory took 50.867 seconds; 600 seconds includes host-load margin.'}
[IO.File]::WriteAllText((Join-Path $outputRoot 'axiom-inventory.json'),($record|ConvertTo-Json -Depth 10),$utf8)
if ($result.TimedOut -or $result.OutputLimitExceeded -or $result.ExitCode -ne 0) { throw 'Axiom inventory failed or inconclusive' }
$expected = @(
 'RMQ.EncodingVariableLowerBound.boundedBitStrings_cardinality',
 'RMQ.ExactRMQBoundedEncoding.shapeEncode_injective_on',
 'RMQ.ExactRMQBoundedEncoding.shapeCount_le',
 'RMQ.ExactRMQBoundedEncoding.doubledLogSlackLower_le',
 'RMQ.SuccinctFinal.PackedWordRAM.deserializeWords_serializeWords',
 'RMQ.SuccinctFinal.PackedWordRAM.serializeWords_injective',
 'RMQ.SuccinctFinal.PackedWordRAM.allocationBits_length',
 'RMQ.SuccinctFinal.PackedWordRAM.reconstructedMemory_eq_buildMemory',
 'RMQ.SuccinctFinal.PackedWordRAM.allocationDecoder_exact',
 'RMQ.SuccinctFinal.PackedWordRAM.allocationBits_shape_injective',
 'RMQ.SuccinctFinal.PackedWordRAM.uniformAllocation_shapeCount_le',
 'RMQ.SuccinctFinal.PackedWordRAM.uniformAllocation_doubledLogSlackLower_le',
 'RMQ.SuccinctFinal.PackedWordRAM.canonicalAllocation_shapeCount_le',
 'RMQ.SuccinctFinal.PackedWordRAM.canonicalAllocation_doubledLogSlackLower_le',
 'RMQ.SuccinctFinal.PackedWordRAM.allocationBits_capacity_le',
 'RMQ.SuccinctFinal.PackedWordRAM.reconstructedRun_eq',
 'RMQ.SuccinctFinal.PackedWordRAM.reconstructedPackedQueryCapstone_holds',
 'RMQ.SuccinctFinal.PackedWordRAM.packedAllocationOptimality_holds',
 'RMQ.Validation.VariablePayloadLowerBound.publicContract',
 'RMQ.Validation.VariablePayloadLowerBound.composedConsumer')
$diagnosticText = $result.StandardOutput -join "`n"
$matches = [regex]::Matches($diagnosticText,"'([^']+)' depends on axioms: \[([^\]]*)\]")
if ($matches.Count -ne $expected.Count) { throw 'Unexpected axiom output count' }
$rows = @()
for($i=0;$i -lt $expected.Count;$i++) {
 if($matches[$i].Groups[1].Value -cne $expected[$i]) { throw ('Unexpected axiom declaration at '+$i) }
 $axioms = @($matches[$i].Groups[2].Value.Split(',') | ForEach-Object {$_.Trim()} | Where-Object {$_})
 foreach($name in $axioms) { if($name -cnotin @('propext','Classical.choice','Quot.sound')) { throw ('Unexpected axiom '+$name) } }
 $rows += [ordered]@{Name=$expected[$i];Axioms=$axioms}
}
if(([regex]::Replace($diagnosticText,"'([^']+)' depends on axioms: \[([^\]]*)\]",'')).Trim()) { throw 'Unclassified axiom stdout' }
if(($result.StandardError -join "`n").Trim()) { throw 'Unclassified axiom stderr' }
$scans = @()
foreach($probe in @(
 [pscustomobject]@{Name='trust-tokens';Arguments=@('-n','\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib','RMQ','lakefile.toml')},
 [pscustomobject]@{Name='native-reduction';Arguments=@('-n','native_decide|Lean\.ofReduceBool','RMQ')})) {
 $scanOutput = @(& rg @($probe.Arguments) 2>&1)
 $scanExit = $LASTEXITCODE
 $scans += [ordered]@{Name=$probe.Name;Command=@('rg')+$probe.Arguments;ExitCode=$scanExit;Output=@($scanOutput|ForEach-Object {"$_"})}
 if($scanExit -ne 1 -or $scanOutput.Count -ne 0) { throw ('Trust source scan requires classification: '+$probe.Name) }
}
foreach($source in $hashes) { if((Get-FileHash -LiteralPath (Join-Path $repo $source.Path)).Hash -cne $source.SHA256) { throw ('Source changed '+$source.Path) } }
$state = Get-RMQRepositoryStateBounded -RepositoryRoot $repo -GitPath $git -DeadlineSeconds 30 -OutputLimitBytes 1048576 -TempRoot $outputRoot -StagePrefix 'trust-final'
Assert-RMQCleanRepositoryStateText $state 'trust-final'
$summary = [ordered]@{Commit=$head;Expected=$expected;Observed=@($rows);Scans=$scans;SourceUnchanged=$true;CleanTree=$true;TrustScope='Reported kernel assumptions; no replacement for expected-type consumers or semantic mutations.'}
[IO.File]::WriteAllText((Join-Path $outputRoot 'summary.json'),($summary|ConvertTo-Json -Depth 10),$utf8)
Write-Host ('LB1-FINAL-TRUST PASS names=20 source-scans=2 evidence='+$outputRoot)
