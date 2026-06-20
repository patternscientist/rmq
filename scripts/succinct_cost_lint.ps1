$ErrorActionPreference = "Stop"

# This lint is intentionally conservative and local to the succinct frontier.
# `Costed.tickValue` is sound Lean, but it is easy to misuse it by charging one
# step for an aggregate reference computation. Keep any matches visible during
# the real 2n+o(n), O(1) succinct-RMQ work.

$matches = rg -n "Costed\.tickValue" RMQ/Core/Succinct.lean RMQ/Core/SuccinctSpace.lean

if ($LASTEXITCODE -eq 1) {
  exit 0
}

if ($LASTEXITCODE -ne 0) {
  exit $LASTEXITCODE
}

Write-Output "Potential asserted succinct-cost charges:"
Write-Output $matches
exit 1
