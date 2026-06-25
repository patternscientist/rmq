import RMQ.Archive.SelectObstructions
import RMQ.Archive.BPSpecializedCapstone

/-!
Compatibility aliases for archived select/access surfaces.

New archive checks should prefer `RMQ.Archive.SelectObstructions` and
`RMQ.Archive.BPSpecializedCapstone` directly. This file keeps older stable
archive import behavior as a thin compatibility root, without retaining the
physically pruned four-field locator island.
-/

namespace RMQ.Archive.SelectCompatibility

/- Old closed RMQ capstone preserved as a compatibility anchor. -/

abbrev builtRelativeSplit_bpNative_total_two_sided_doubled_catalan_slack_profile :=
  RMQ.Archive.BPSpecializedCapstone.total_two_sided_doubled_catalan_slack_profile

end RMQ.Archive.SelectCompatibility
