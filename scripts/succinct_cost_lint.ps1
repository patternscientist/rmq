$ErrorActionPreference = "Stop"

# This lint is intentionally conservative and local to the succinct frontier.
# `Costed.tickValue` is sound Lean, but it is easy to misuse it by charging one
# step for an aggregate reference computation. Keep any matches visible during
# the real 2n+o(n), O(1) succinct-RMQ work.

$tickValueMatches = rg -n "Costed\.tickValue" RMQ/Core/Succinct.lean RMQ/Core/SuccinctSpace.lean

if ($LASTEXITCODE -ne 0 -and $LASTEXITCODE -ne 1) {
  exit $LASTEXITCODE
}

$littleOPattern = "LittleOLinear\s*\(\s*fun\s+_\s*=>"
$littleOMatches = rg -n -U $littleOPattern `
  RMQ/Core/SuccinctRankProposal.lean `
  RMQ/Core/SuccinctSelectProposal.lean `
  RMQ/Core/SuccinctSelect `
  RMQ/Core/SuccinctCloseProposal.lean `
  RMQ/Core/SuccinctFinal.lean

if ($LASTEXITCODE -ne 0 -and $LASTEXITCODE -ne 1) {
  exit $LASTEXITCODE
}

$fullRankGuardPattern = "if\s+.*rankPrefix\s+false\s+shape\.bpCode\s+shape\.bpCode\.length\s+then"
$fullRankGuardMatches = rg -n $fullRankGuardPattern `
  RMQ/Core/SuccinctSelectProposal.lean `
  RMQ/Core/SuccinctSelect `
  RMQ/Core/SuccinctFinal.lean

if ($LASTEXITCODE -ne 0 -and $LASTEXITCODE -ne 1) {
  exit $LASTEXITCODE
}

$failed = $false

if ($tickValueMatches) {
  Write-Output "Potential asserted succinct-cost charges:"
  Write-Output $tickValueMatches
  $failed = $true
}

if ($littleOMatches) {
  Write-Output "Potential vacuous constant-function LittleOLinear claims:"
  Write-Output $littleOMatches
  Write-Output "Use an overhead function of n plus an explicit payload.length <= overhead n bound."
  $failed = $true
}

if ($fullRankGuardMatches) {
  Write-Output "Potential uncharged full-list false-rank guard in a costed query:"
  Write-Output $fullRankGuardMatches
  Write-Output "Use a cheap shape/index guard in executable code and keep full-count facts proof-only."
  $failed = $true
}

if ($failed) {
  exit 1
}

exit 0
