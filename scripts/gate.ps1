#!/usr/bin/env pwsh
# RMQ autonomous-loop acceptance gate.
#
# Exit 0  = ACCEPT: the round is sound and non-regressing; the loop may continue.
# Exit !=0 = STOP: surface to the human (or retry once, then stop).
#
# This gate proves soundness and non-regression. It does NOT prove the round
# moved the needle -- that is the roadmap / anti-filler contract's job
# (see docs/CODEX_AUTONOMY.md and docs/ROADMAP.md).

$ErrorActionPreference = 'Continue'

function Fail($msg) { Write-Host "GATE FAIL: $msg"; exit 1 }

# 1. Build must be green.
lake build
if ($LASTEXITCODE -ne 0) { Fail "lake build failed" }

lake build RMQHub
if ($LASTEXITCODE -ne 0) { Fail "lake build RMQHub failed" }

lake build RMQRankSelect
if ($LASTEXITCODE -ne 0) { Fail "lake build RMQRankSelect failed" }

lake build RMQArchive
if ($LASTEXITCODE -ne 0) { Fail "lake build RMQArchive failed" }

# 2. Proof-hygiene scan: any hit fails the gate.
$hygiene = rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ RMQHub.lean RMQRankSelect.lean RMQArchive.lean lakefile.toml
if ($hygiene) { Fail "hygiene scan hit:`n$hygiene" }

$nd = rg -n "native_decide|Lean\.ofReduceBool" RMQ RMQHub.lean RMQRankSelect.lean RMQArchive.lean
if ($nd) { Fail "native_decide / ofReduceBool present in source:`n$nd" }

# 3. Curated trust-base check: load-bearing theorems use only standard axioms.
$ax = lake env lean scripts/axiom_check.lean
if ($LASTEXITCODE -ne 0) { Fail "axiom_check.lean did not run cleanly" }
if ($ax | Select-String -Pattern "sorryAx|ofReduceBool") {
  Fail "non-standard axiom in a load-bearing theorem:`n$ax"
}

$archiveAx = lake env lean scripts/archive_axiom_check.lean
if ($LASTEXITCODE -ne 0) { Fail "archive_axiom_check.lean did not run cleanly" }
if ($archiveAx | Select-String -Pattern "sorryAx|ofReduceBool") {
  Fail "non-standard axiom in an archived compatibility theorem:`n$archiveAx"
}

$rankSelectAx = lake env lean scripts/rank_select_axiom_check.lean
if ($LASTEXITCODE -ne 0) { Fail "rank_select_axiom_check.lean did not run cleanly" }
if ($rankSelectAx | Select-String -Pattern "sorryAx|ofReduceBool") {
  Fail "non-standard axiom in a rank/select theorem:`n$rankSelectAx"
}

# 4. Succinct frontier cost/space lints.
& "$PSScriptRoot\succinct_cost_lint.ps1"
if ($LASTEXITCODE -ne 0) { Fail "succinct_cost_lint.ps1 found issues" }

# 5. Compatibility-shim import boundary.
& "$PSScriptRoot\shim_lint.ps1"
if ($LASTEXITCODE -ne 0) { Fail "shim_lint.ps1 found issues" }

# 6. Whitespace / leftover merge markers.
git diff --check
if ($LASTEXITCODE -ne 0) { Fail "git diff --check found issues" }

Write-Host "GATE PASS"
exit 0
