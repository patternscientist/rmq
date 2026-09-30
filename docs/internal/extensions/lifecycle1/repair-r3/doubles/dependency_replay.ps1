[CmdletBinding()]
param([switch]$SelectorProbeOnly,[AllowEmptyString()][string]$OnlyCase,[switch]$SelfTestOnly,[switch]$StartupOnly,
  [int]$DeadlineSeconds=120,[string]$EvidenceDirectory)
# LIFE-1-R3 test double for the production dependency replay invoked in-process by
# dependency_child.ps1 (disposable copy only). It answers only the D07 selector.
$ErrorActionPreference='Stop'
# R3-FAULT-FUNCTION
if(Invoke-R3Fault){[Console]::Error.WriteLine('R3-DOUBLE: injected ordinary stage failure');exit 23}
if([Environment]::GetEnvironmentVariable('LIFE1_DEPENDENCY_SELECTOR') -ceq 'id:D01_CONSTRUCTION'){
  Write-Output 'LIFE1-DEPENDENCY SELECT D01_CONSTRUCTION'
  exit 0
}
[Console]::Error.WriteLine('R3-DOUBLE: unsupported selector')
exit 2
