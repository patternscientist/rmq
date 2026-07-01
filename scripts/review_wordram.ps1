#!/usr/bin/env pwsh
# Focused reviewer check for the Word-RAM anti-oracle boundary.
#
# This is deliberately narrower than gate.ps1. It builds the interpreter,
# the public interpreted capstones, and the small examples, then prints the
# trust base for the interpreter provenance lemmas and interpreted theorem
# surfaces.

$ErrorActionPreference = 'Continue'

function Fail($msg) {
  Write-Host "WORDRAM REVIEW FAIL: $msg"
  exit 1
}

Write-Host "== Build WordRAM and interpreted public roots =="
lake build RMQ.Core.WordRAM RMQ.Core.RankSelectPublicRAM RMQ.Core.SuccinctFinalRAM RMQ.Headlines RMQExamples
if ($LASTEXITCODE -ne 0) { Fail "Lean build failed" }

Write-Host "== WordRAM theorem axioms =="
$ax = lake env lean scripts/wordram_axiom_check.lean
if ($LASTEXITCODE -ne 0) { Fail "wordram_axiom_check.lean did not run cleanly" }
Write-Host $ax
if ($ax | Select-String -Pattern "sorryAx|Lean\.ofReduceBool|ofReduceBool") {
  Fail "non-standard axiom in WordRAM theorem surface"
}

Write-Host "== Hygiene =="
$hygiene = rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ RMQExamples RMQRankSelect.lean RMQExamples.lean lakefile.toml
if ($hygiene) { Fail "hygiene scan hit:`n$hygiene" }

$nd = rg -n "native_decide|Lean\.ofReduceBool" RMQ RMQExamples RMQRankSelect.lean RMQExamples.lean
if ($nd) { Fail "native_decide / ofReduceBool present in source:`n$nd" }

git diff --check
if ($LASTEXITCODE -ne 0) { Fail "git diff --check found issues" }

Write-Host "WORDRAM REVIEW PASS"
exit 0
