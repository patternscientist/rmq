import RMQ.Archive.SelectObstructions
import RMQ.Archive.BPSpecializedCapstone

/-!
Compatibility aliases for archived select/access surfaces.

New archive checks should prefer `RMQ.Archive.SelectObstructions` and
`RMQ.Archive.BPSpecializedCapstone` directly. This file keeps the older stable
names as a thin compatibility root.
-/

namespace RMQ.Archive.SelectCompatibility

/- BP-specialized sparse/dense false-select obstruction anchor. -/

abbrev sparseDense_locator_fullMachineField_not_word_bounded :=
  RMQ.Archive.SelectObstructions.sparseDense_locator_fullMachineField_not_word_bounded

/- Old closed RMQ capstone preserved as a compatibility anchor. -/

abbrev builtRelativeSplit_bpNative_total_two_sided_doubled_catalan_slack_profile :=
  RMQ.Archive.BPSpecializedCapstone.total_two_sided_doubled_catalan_slack_profile

end RMQ.Archive.SelectCompatibility
