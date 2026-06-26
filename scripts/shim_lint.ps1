#!/usr/bin/env pwsh
# Keep compatibility shims out of live repository roots.
#
# The historical proposal modules and old flat GenericSelect files are retained
# for downstream imports, but new in-repository code should use the canonical
# split roots instead.  This lint makes that cleanup boundary explicit.

$ErrorActionPreference = 'Continue'

function Fail($msg) { Write-Host "SHIM LINT FAIL: $msg"; exit 1 }

$scanRoots = @(
  "RMQ",
  "RMQ.lean",
  "RMQHub.lean",
  "RMQRankSelect.lean",
  "RMQArchive.lean",
  "RMQExamples.lean",
  "RMQExamples",
  "scripts",
  "docs"
)

$shimImportPattern = "import RMQ\.Core\.(SuccinctRankProposal|SuccinctSelectProposal|SuccinctCloseProposal|GenericSelectBuilder|GenericSelectParams|GenericSelectPrimitives)"
$shimImports = rg -n $shimImportPattern @scanRoots
if ($LASTEXITCODE -ne 0 -and $LASTEXITCODE -ne 1) {
  Fail "rg failed while scanning compatibility-shim imports"
}
if ($shimImports) {
  Fail "live compatibility-shim imports found:`n$shimImports"
}

$proposalOpenPattern = "open RMQ\.(SuccinctRankProposal|SuccinctSelectProposal|SuccinctCloseProposal)"
$proposalOpens = rg -n $proposalOpenPattern @scanRoots
if ($LASTEXITCODE -ne 0 -and $LASTEXITCODE -ne 1) {
  Fail "rg failed while scanning proposal namespace opens"
}
if ($proposalOpens) {
  Fail "live proposal namespace opens found:`n$proposalOpens"
}

Write-Host "SHIM LINT PASS"
exit 0
