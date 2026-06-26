import RMQ.Core.EncodingLowerBound

/-!
# Minimal lower-bound import example

This imports only the RMQ encoding lower-bound layer and names the tight
fixed-length payload-space theorem with doubled Catalan slack.
-/

namespace RMQ.Examples.LowerBoundImport

abbrev exactRMQPayloadLowerBound :=
  RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack

end RMQ.Examples.LowerBoundImport
