import RMQ
import RMQHub
import RMQRankSelect
import RMQBPNavigation
import RMQUnionFind

/-!
# VerifiedDS aggregate facade

Neutral import root for the verified data-structures library growing out of the
RMQ proof-of-concept.  This file is intentionally only a thin facade over the
current public roots:

- `RMQ` for the RMQ/LCA family and succinct RMQ capstone;
- `RMQHub` for reusable cost, RAM, refinement, table, and lower-bound layers;
- `RMQRankSelect` for the standalone rank/select spoke;
- `RMQBPNavigation` for the balanced-parentheses navigation spoke; and
- `RMQUnionFind` for the union-find specification and forest-refinement spoke.

The old roots remain canonical and citable.  This facade signals the broader
library direction without forcing a repository or namespace migration before the
spoke APIs settle.
-/
