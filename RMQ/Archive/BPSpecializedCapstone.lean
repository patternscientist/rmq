import RMQ.Core.SuccinctFinal

/-!
Archived BP-specialized succinct RMQ capstone.

The public path now uses the generic sparse-exception select source over
`shape.bpCode`. This module intentionally keeps the older relative-split
BP-specialized capstone as a checked historical result, not as a headline.
-/

namespace RMQ.Archive.BPSpecializedCapstone

abbrev total_two_sided_doubled_catalan_slack_profile :=
  RMQ.SuccinctFinal.builtRelativeSplitSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile

end RMQ.Archive.BPSpecializedCapstone
