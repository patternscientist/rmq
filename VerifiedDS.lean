import VerifiedDS.Hub
import VerifiedDS.RMQ
import VerifiedDS.RankSelect
import VerifiedDS.BPNavigation
import VerifiedDS.UnionFind

/-!
# VerifiedDS aggregate facade

Neutral import root for the verified data-structures library growing out of the
RMQ proof-of-concept.  This file is intentionally only a thin facade over the
current public roots, now with neutral role modules:

- `VerifiedDS.Hub` over `RMQHub`;
- `VerifiedDS.RMQ` over `RMQ`;
- `VerifiedDS.RankSelect` over `RMQRankSelect`;
- `VerifiedDS.BPNavigation` over `RMQBPNavigation`; and
- `VerifiedDS.UnionFind` over `RMQUnionFind`.

The old roots remain canonical and citable. These facades signal the broader
library direction without forcing a repository or namespace migration before
the spoke APIs settle.
-/
