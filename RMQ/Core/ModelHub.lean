import RMQ.Core.Cost
import RMQ.Core.Amortized
import RMQ.Core.AmortizedSequence
import RMQ.Core.RAM
import RMQ.Core.Refine
import RMQ.Core.TableModel
import RMQ.Core.LowerBound
import RMQ.Core.PayloadLowerBound

/-!
# Reusable model hub

This import-only module names the RMQ-free reusable layer of the proof of
concept.  It deliberately excludes RMQ ranges, Cartesian shapes, Euler tours,
and backend implementations.
-/
