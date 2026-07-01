import RMQ.Core.BPNavigationPublic

/-!
# Balanced-parentheses navigation spoke

This import root exposes the compact balanced-parentheses close/LCA navigation
surface used by the succinct RMQ capstone. It is intentionally narrower than a
full tree-navigation library: the public API includes the close/rank bridge
over Cartesian-shape BP encodings, the rank-backed excess and close/excess
bridge, a charged subtree-interval operation, a conditional fast
matching-open-backed subtree-interval operation, a dense concrete
matching-open/enclose directory with constant-query parent-open/enclose
navigation, a public constant-query parent-index operation, plus close-position
LCA navigation, with exactness and
payload/word-bound profiles exposed through `RMQ.BPNavigation`.

The public bridge/profile theorems are
`RMQ.BPNavigation.shapeAccessCloseRankProfile`,
`RMQ.BPNavigation.shapeAccessCloseRankExcessProfile`,
`RMQ.BPNavigation.shapeAccessSubtreeIntervalProfile`,
`RMQ.BPNavigation.shapeAccessFastSubtreeIntervalProfile`, and
`RMQ.BPNavigation.shapeAccessEncloseOpenProfile`,
`RMQ.BPNavigation.shapeAccessParentProfile`, together with the concrete
profiles `RMQ.BPNavigation.ConcreteMatchingOpenEncloseDirectory.profile`,
`RMQ.BPNavigation.concreteShapeAccessFastSubtreeIntervalProfile`, and
`RMQ.BPNavigation.concreteShapeAccessEncloseOpenProfile`,
`RMQ.BPNavigation.concreteShapeAccessParentProfile`, plus
`RMQ.BPNavigation.compactCloseDirectoryProfile`.
-/
