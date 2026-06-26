import RMQ.Core.BPNavigationPublic

/-!
# Balanced-parentheses navigation spoke

This import root exposes the compact balanced-parentheses close/LCA navigation
surface used by the succinct RMQ capstone. It is intentionally narrower than a
full tree-navigation library: the public API is close-position LCA navigation
over Cartesian-shape BP encodings, with exactness and payload/word-bound
profiles exposed through `RMQ.BPNavigation`.

The public concrete profile is
`RMQ.BPNavigation.compactCloseDirectoryProfile`.
-/
