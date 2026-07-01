import RMQ.Core.SuccinctSpace.BPCloseRMQNavigation
import RMQ.Core.SuccinctSpace.TablesRAM
import RMQ.Core.SuccinctSpace.SelectSamplesRAM
import RMQ.Core.SuccinctSpace.RankSelectRAM
import RMQ.Core.SuccinctSpace.BPCloseLCARAM
import RMQ.Core.SuccinctSpace.BPCloseRMQNavigationRAM

/-!
# Succinct RMQ space/profile interface

This is the public barrel for the role-split succinct-space layer.  The
component modules separate the asymptotic payload model, word/table encodings,
rank/select and balanced-parentheses access, broadword RMQ profiles, and the
BP close-navigation wrapper used by the final succinct RMQ theorem.

The layer does not assert that Lean's executable representation is a
machine-word implementation.  Instead, it packages the standard word-RAM claim
shape: an exact `2*n` Cartesian-shape payload, counted auxiliary payload bits,
a constant-cost query decoder under the explicit RAM model, and an `o(n)`
auxiliary payload budget.
-/
