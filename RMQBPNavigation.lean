import RMQ.Core.BPNavigationPublic

/-!
# Balanced-parentheses navigation spoke

This import root exposes the compact balanced-parentheses close/LCA navigation
surface used by the succinct RMQ capstone. It is intentionally narrower than a
full tree-navigation library: the public API includes the close/rank bridge
over Cartesian-shape BP encodings, the rank-backed excess and close/excess
bridge, plus close-position LCA navigation, with exactness and
payload/word-bound profiles exposed through `RMQ.BPNavigation`.

The public bridge/profile theorems are
`RMQ.BPNavigation.shapeAccessCloseRankProfile`,
`RMQ.BPNavigation.shapeAccessCloseRankExcessProfile`, and
`RMQ.BPNavigation.compactCloseDirectoryProfile`.
-/
