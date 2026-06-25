import RMQ.Archive.SelectObstructions
import RMQ.Archive.BPSpecializedCapstone

/-!
Checked archive trust-base inventory.

This file is deliberately small: it checks only retained obstruction witnesses
and the old BP-specialized relative-split capstone. Superseded prototype table
profiles and intermediate adapters should not be kept alive solely by this
archive gate.
-/

/- BP-specialized sparse/dense obstruction witnesses. -/

#print axioms RMQ.Archive.SelectObstructions.sparseDense_locator_fullMachineField_not_word_bounded
#print axioms RMQ.Archive.SelectObstructions.short_super_local_pointer_capacity_obstruction
#print axioms RMQ.Archive.SelectObstructions.dense_branch_packed_local_pointer_capacity_obstruction
#print axioms RMQ.Archive.SelectObstructions.super_locator_full_machine_field_impossible
#print axioms RMQ.Archive.SelectObstructions.local_locator_full_machine_field_impossible

/- Old BP-specialized relative-split capstone retained for compatibility. -/

#print axioms RMQ.Archive.BPSpecializedCapstone.total_two_sided_doubled_catalan_slack_profile
