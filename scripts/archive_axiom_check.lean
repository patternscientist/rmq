import RMQ.Archive.SelectObstructions
import RMQ.Archive.BPSpecializedCapstone

/-!
Checked archive trust-base inventory.

This file is deliberately small: it checks only retained obstruction witnesses
and the old BP-specialized relative-split capstone. Superseded prototype table
profiles and intermediate adapters should not be kept alive solely by this
archive gate.
-/

/- Select-side obstruction witnesses retained after pruning old locator code. -/

#print axioms RMQ.Archive.SelectObstructions.shared_aligned_read_word_forces_same_wordIndex
#print axioms RMQ.Archive.SelectObstructions.shared_local_locator_forces_same_selected_wordIndex
#print axioms RMQ.Archive.SelectObstructions.shared_local_locator_contradicts_distinct_selected_wordIndex

/- Old BP-specialized relative-split capstone retained for compatibility. -/

#print axioms RMQ.Archive.BPSpecializedCapstone.total_two_sided_doubled_catalan_slack_profile
