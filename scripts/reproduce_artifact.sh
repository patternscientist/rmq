#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

echo "== Tool versions =="
if command -v elan >/dev/null 2>&1; then
  elan --version
else
  echo "elan not found on PATH"
fi
lean --version
lake --version

echo "== lake build =="
lake build

echo "== headline axiom check =="
lake env lean scripts/headline_axiom_check.lean

echo "== WordRAM axiom check =="
lake env lean scripts/wordram_axiom_check.lean

echo "== full axiom check =="
lake env lean scripts/axiom_check.lean

echo "== forbidden source tokens =="
forbidden_source_re='\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib'
if rg -n "$forbidden_source_re" RMQ lakefile.toml; then
  echo "Forbidden source token scan failed"
  exit 1
fi
echo "No forbidden source tokens found"

echo "== forbidden reduction shortcuts =="
if rg -n 'native_decide|Lean\.ofReduceBool' RMQ; then
  echo "Forbidden reduction shortcut scan failed"
  exit 1
fi
echo "No forbidden reduction shortcuts found"

echo "== whitespace diff check =="
git diff --check

echo "Artifact reproduction completed successfully"
