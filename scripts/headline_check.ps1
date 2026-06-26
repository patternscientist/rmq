#!/usr/bin/env pwsh
# Public headline verification path. This is intentionally shorter than
# gate.ps1: it checks the build, the headline theorem trust base, and the basic
# hygiene claims summarized in README.md.

$ErrorActionPreference = 'Continue'

function Fail($msg) {
  Write-Host "HEADLINE CHECK FAIL: $msg"
  exit 1
}

Write-Host "== Build =="
lake build
if ($LASTEXITCODE -ne 0) { Fail "lake build failed" }

lake build RMQExamples
if ($LASTEXITCODE -ne 0) { Fail "lake build RMQExamples failed" }

Write-Host "== Headline theorem axioms =="
$ax = lake env lean scripts/headline_axiom_check.lean
if ($LASTEXITCODE -ne 0) { Fail "headline_axiom_check.lean did not run cleanly" }
Write-Host $ax
if ($ax | Select-String -Pattern "sorryAx|Lean\.ofReduceBool|ofReduceBool") {
  Fail "non-standard axiom in a headline theorem"
}

Write-Host "== Hygiene =="
$hygiene = rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ RMQExamples RMQExamples.lean lakefile.toml
if ($hygiene) { Fail "hygiene scan hit:`n$hygiene" }

$nd = rg -n "native_decide|Lean\.ofReduceBool" RMQ RMQExamples RMQExamples.lean
if ($nd) { Fail "native_decide / ofReduceBool present in source:`n$nd" }

git diff --check
if ($LASTEXITCODE -ne 0) { Fail "git diff --check found issues" }

Write-Host "HEADLINE CHECK PASS"
exit 0
