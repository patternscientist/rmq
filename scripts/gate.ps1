#!/usr/bin/env pwsh
# RMQ autonomous-loop acceptance gate.
#
# Exit 0  = ACCEPT: the round is sound and non-regressing; the loop may continue.
# Exit !=0 = STOP: surface to the human (or retry once, then stop).
#
# This gate proves soundness and non-regression. It does NOT prove the round
# moved the needle -- that is the roadmap / anti-filler contract's job
# (see docs/internal/CODEX_AUTONOMY.md and docs/ROADMAP.md).

$ErrorActionPreference = 'Continue'

function Fail($msg) { Write-Host "GATE FAIL: $msg"; exit 1 }

function RunAxiomCheck($script, $label) {
  $tmp = New-TemporaryFile
  & lake env lean $script 2>&1 | Tee-Object -FilePath $tmp
  $code = $LASTEXITCODE
  if ($code -ne 0) {
    Remove-Item $tmp -ErrorAction SilentlyContinue
    Fail "$label did not run cleanly"
  }
  if (Select-String -Path $tmp -Pattern "sorryAx|ofReduceBool") {
    $bad = Get-Content $tmp
    Remove-Item $tmp -ErrorAction SilentlyContinue
    Fail "non-standard axiom in ${label}:`n$bad"
  }
  Remove-Item $tmp -ErrorAction SilentlyContinue
}

# 1. Build must be green.
lake build
if ($LASTEXITCODE -ne 0) { Fail "lake build failed" }

lake build RMQHub
if ($LASTEXITCODE -ne 0) { Fail "lake build RMQHub failed" }

lake build RMQRankSelect
if ($LASTEXITCODE -ne 0) { Fail "lake build RMQRankSelect failed" }

lake build RMQBPNavigation
if ($LASTEXITCODE -ne 0) { Fail "lake build RMQBPNavigation failed" }

lake build RMQUnionFind
if ($LASTEXITCODE -ne 0) { Fail "lake build RMQUnionFind failed" }

lake build VerifiedDS
if ($LASTEXITCODE -ne 0) { Fail "lake build VerifiedDS failed" }

lake build RMQArchive
if ($LASTEXITCODE -ne 0) { Fail "lake build RMQArchive failed" }

lake build RMQExamples
if ($LASTEXITCODE -ne 0) { Fail "lake build RMQExamples failed" }

lake build RMQ.Core.GenericSelectBPCompat
if ($LASTEXITCODE -ne 0) { Fail "lake build RMQ.Core.GenericSelectBPCompat failed" }

# 2. Proof-hygiene scan: any hit fails the gate.
$hygiene = rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ RMQExamples RMQHub.lean RMQRankSelect.lean RMQBPNavigation.lean RMQUnionFind.lean VerifiedDS.lean RMQArchive.lean RMQExamples.lean lakefile.toml
if ($hygiene) { Fail "hygiene scan hit:`n$hygiene" }

$nd = rg -n "native_decide|Lean\.ofReduceBool" RMQ RMQExamples RMQHub.lean RMQRankSelect.lean RMQBPNavigation.lean RMQUnionFind.lean VerifiedDS.lean RMQArchive.lean RMQExamples.lean
if ($nd) { Fail "native_decide / ofReduceBool present in source:`n$nd" }

# 3. Curated trust-base check: load-bearing theorems use only standard axioms.
RunAxiomCheck "scripts/hub_axiom_check.lean" "hub_axiom_check.lean"
RunAxiomCheck "scripts/axiom_check.lean" "axiom_check.lean"
RunAxiomCheck "scripts/archive_axiom_check.lean" "archive_axiom_check.lean"
RunAxiomCheck "scripts/rank_select_axiom_check.lean" "rank_select_axiom_check.lean"
RunAxiomCheck "scripts/bp_navigation_axiom_check.lean" "bp_navigation_axiom_check.lean"
RunAxiomCheck "scripts/union_find_axiom_check.lean" "union_find_axiom_check.lean"

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
