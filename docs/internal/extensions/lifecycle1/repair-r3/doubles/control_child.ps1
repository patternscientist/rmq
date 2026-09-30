param([string]$SpecPath,[string]$RepositoryRoot,[string]$EvidenceRoot)
# LIFE-1-R3 test double for a run_controls.ps1 handler child (disposable copy only).
$ErrorActionPreference='Stop'
# R3-FAULT-FUNCTION
$spec=[IO.File]::ReadAllText($SpecPath)|ConvertFrom-Json
if(Invoke-R3Fault){[Console]::Error.WriteLine('R3-DOUBLE: injected ordinary child failure');exit 23}
Write-Output ('L1R1-CONTROL|'+$spec.id+'|PASS')
exit 0
