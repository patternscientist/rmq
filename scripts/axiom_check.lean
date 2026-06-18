import RMQ

/-!
Curated trust-base check for the acceptance gate.

`scripts/gate.ps1` runs this file with `lake env lean` and fails the gate if any
listed theorem depends on a non-standard axiom -- e.g. `sorryAx` (from `sorry`)
or `Lean.ofReduceBool` (from `native_decide`). Standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) are allowed.

Extend this list whenever a new *headline* theorem lands (a theorem a researcher
would cite, not a `_value/_erase/_cost/_run` helper). Keeping the list focused on
load-bearing results is the point: it pins the trust base of the claims that
matter, not every lemma.
-/

#print axioms RMQ.scanWindow_leftmost
#print axioms RMQ.RMQBackend.queryBuilt_eq
#print axioms RMQ.Cartesian.shape_eq_of_sameRMQBehavior
#print axioms RMQ.EncodingLowerBound.shapeCount_quadratic_lower
#print axioms RMQ.EncodingLowerBound.two_mul_sub_log_slack_le_bits_of_exactRMQShapeEncoding
#print axioms RMQ.FischerHeun.linearBuild_constantQuery_profile
#print axioms RMQ.FischerHeun.queryWithStateCosted_cost_le_eight_of_blockSize_pos
#print axioms RMQ.FischerHeun.buildWithBlockSizeCosted_value
