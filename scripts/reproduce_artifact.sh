#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

section() {
  echo
  echo "== $1 =="
}

echo "== Tool versions =="
if command -v elan >/dev/null 2>&1; then
  elan --version
else
  echo "elan not found on PATH"
fi
lean --version
lake --version

section "lake build"
lake build

section "public root builds for axiom checks"
lake build RMQPaper
lake build RMQHub
lake build RMQRankSelect
lake build RMQBPNavigation
lake build RMQUnionFind
lake build VerifiedDS
lake build RMQArchive
lake build RMQExamples
lake build RMQ.Core.GenericSelectBPCompat

section "classic RMQ concrete validation"
lake exe rmq_succinct_classic_validate

section "classic RMQ executable cost harness"
lake exe rmq_succinct_classic_cost_harness

section "headline axiom check"
lake env lean scripts/headline_axiom_check.lean

section "WordRAM axiom check"
lake env lean scripts/wordram_axiom_check.lean

section "full axiom check"
lake env lean scripts/axiom_check.lean

section "full repository gate"
if command -v pwsh >/dev/null 2>&1; then
  pwsh -NoLogo -NoProfile -ExecutionPolicy Bypass -File scripts/gate.ps1
elif [[ "${CI:-}" == "true" ]]; then
  echo "pwsh is required for scripts/gate.ps1 in CI"
  exit 1
else
  echo "pwsh not found; skipping scripts/gate.ps1 outside CI"
fi

section "forbidden source tokens"
forbidden_source_re='\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib'
if rg -n "$forbidden_source_re" RMQ RMQPaper.lean lakefile.toml; then
  echo "Forbidden source token scan failed"
  exit 1
fi
echo "No forbidden source tokens found"

section "forbidden reduction shortcuts"
if rg -n 'native_decide|Lean\.ofReduceBool' RMQ RMQPaper.lean; then
  echo "Forbidden reduction shortcut scan failed"
  exit 1
fi
echo "No forbidden reduction shortcuts found"

section "whitespace dirty-tree diff check"
git diff --check

section "whitespace committed-patch diff check"
if git rev-parse --verify HEAD^ >/dev/null 2>&1; then
  git diff --check HEAD^..HEAD
else
  echo "No HEAD^ commit; skipping committed-patch whitespace check"
fi

echo "Artifact reproduction completed successfully"
