import RMQ.Archive.SelectCompatibility

/-!
Checked archive trust-base inventory.

This file is deliberately small: it checks only retained obstruction witnesses
and the old BP-specialized relative-split capstone. Superseded prototype table
profiles and intermediate adapters should not be kept alive solely by this
archive gate.
-/

/- BP-specialized sparse/dense obstruction witnesses. -/

#print axioms RMQ.Archive.SelectCompatibility.sparseDense_locator_fullMachineField_not_word_bounded
#print axioms RMQ.SuccinctSelectProposal.SparseDenseFalseSelectCloseData.short_super_local_pointer_capacity_obstruction
#print axioms RMQ.SuccinctSelectProposal.SparseDenseFalseSelectCloseData.dense_branch_packed_local_pointer_capacity_obstruction
#print axioms RMQ.SuccinctSelectProposal.SparseDenseFalseSelectCloseData.super_locator_full_machine_field_impossible
#print axioms RMQ.SuccinctSelectProposal.SparseDenseFalseSelectCloseData.local_locator_full_machine_field_impossible

/- Old BP-specialized relative-split capstone retained for compatibility. -/

#print axioms RMQ.Archive.SelectCompatibility.builtRelativeSplit_bpNative_total_two_sided_doubled_catalan_slack_profile
