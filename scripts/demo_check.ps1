#!/usr/bin/env pwsh
# Demo-facing verification path. This is intentionally shorter than gate.ps1:
# it checks the build, the headline theorem trust base, and the basic hygiene
# claims that appear in docs/DEMO_GUIDE.md.

$ErrorActionPreference = 'Continue'

function Fail($msg) {
  Write-Host "DEMO CHECK FAIL: $msg"
  exit 1
}

Write-Host "== Build =="
lake build
if ($LASTEXITCODE -ne 0) { Fail "lake build failed" }

Write-Host "== Headline theorem axioms =="
$ax = lake env lean scripts/demo_axiom_check.lean
if ($LASTEXITCODE -ne 0) { Fail "demo_axiom_check.lean did not run cleanly" }
Write-Host $ax
if ($ax | Select-String -Pattern "sorryAx|Lean\.ofReduceBool|ofReduceBool") {
  Fail "non-standard axiom in a demo headline theorem"
}

Write-Host "== Hygiene =="
$hygiene = rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ lakefile.toml
if ($hygiene) { Fail "hygiene scan hit:`n$hygiene" }

$nd = rg -n "native_decide|Lean\.ofReduceBool" RMQ
if ($nd) { Fail "native_decide / ofReduceBool present in source:`n$nd" }

git diff --check
if ($LASTEXITCODE -ne 0) { Fail "git diff --check found issues" }

Write-Host "DEMO CHECK PASS"
exit 0
