# Claim Drift Policy

Claim-drift scans are tripwires, not doctrine. They find sensitive language and
force a policy decision: current, qualified, legacy-only, historical, forbidden,
or intentionally superseded.

When theorem work genuinely changes the public truth, update the checked
theorem surface, public docs, this policy, and the relevant design-decision log
together.

## Evidence Standard

Each sensitive claim should identify its evidence tier:

- kernel theorem;
- model theorem;
- executable validation;
- artifact evidence;
- process evidence.

Process evidence is never enough for a mathematical or executable claim.

## Supersession Rule

If a claim is superseded, do not merely delete it from the scan. Change its
policy:

- current claim -> legacy compatibility;
- current blocker -> historical blocker;
- public theorem constant -> old theorem alias;
- future-work gap -> closed, with theorem or artifact evidence.

The scan should then fail only when old wording appears as the current public
story.

## Policy Data

`scripts/claim_drift_scan.ps1` reads
`docs/internal/CLAIM_DRIFT_POLICY.json`. Keep the JSON concise and update this
human-readable file when the interpretation changes.

## Initial Sensitive Claims

- Novelty language such as "first mechanized" or "first-ever" must be qualified
  by a referee-grade novelty-search caveat unless a future paper process closes
  that search.
- "Logs cannot be forged" must be scoped to interpreter-generated traces and
  checked provenance/model theorems.
- "Artifact ready" and "AE-ready" should only appear when the artifact status is
  actually being claimed.
- "Lean runtime" should not be presented as the RAM model-cost theorem.
- `2^128` is compatibility/history language, not the current public activation
  route.
- `4144` is the current clean fixed all-size bound from the route-split
  theorem; `196727` should be described only as legacy compatibility.
- `118` is the fast-regime modeled bound under the readiness threshold, not the
  all-size theorem unless a future theorem proves that.
- "No extraction gap" must not erase the remaining executable/compiler ladder;
  Lean executability is evidence about runnable definitions, not a verified
  backend.
