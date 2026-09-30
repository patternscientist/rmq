# LIFE-1-R3 test double for a run_check.ps1 external stage (disposable copy only).
$ErrorActionPreference='Stop'
# R3-FAULT-FUNCTION
if(Invoke-R3Fault){[Console]::Error.WriteLine('R3-DOUBLE: injected ordinary stage failure');exit 7}
Write-Output 'R3-STAGE PASS'
exit 0
