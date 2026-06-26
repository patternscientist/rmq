# Balanced-Parentheses Navigation Spoke

Snapshot: 2026-06-26. This note records the extracted public surface for the
compact balanced-parentheses close/LCA navigation layer used by the succinct
RMQ capstone, plus the first public tree-navigation bridge over BP
rank/select.

## Import

Use the standalone import root:

```lean
import RMQBPNavigation
```

`RMQBPNavigation` exposes neutral names under `RMQ.BPNavigation`. It is still a
narrow spoke, but it now exposes the two basic charged BP-navigation legs over
Cartesian-shape balanced-parentheses encodings:

- `closeOfInorderCosted`: inorder node index to closing parenthesis, routed
  through false-select;
- `inorderOfCloseCosted`: closing parenthesis to inorder node index, routed
  through false-rank at `close + 1`.

It is not yet a complete tree-navigation library.

Verification:

```powershell
lake build RMQBPNavigation
lake env lean scripts/bp_navigation_axiom_check.lean
```

## Public Surface

The rank/select-backed tree-navigation bridge is exposed as:

```lean
RMQ.BPNavigation.BalancedParensAccess
RMQ.BPNavigation.closeOfInorderCosted
RMQ.BPNavigation.inorderOfCloseCosted
RMQ.BPNavigation.shapeAccessCloseRankProfile
```

The bridge profile proves one-query modeled cost for both directions, exact
agreement with `SuccinctSpace.bpCloseOfInorder?`, and exact recovery of the
inorder index when the supplied close position comes from
`bpCloseOfInorder?`.

The concrete compact close/LCA directory is exposed as:

```lean
RMQ.BPNavigation.compactCloseDirectory
RMQ.BPNavigation.compactCloseDirectoryProfile
```

The profile proves:

- auxiliary close-navigation payload is bounded by
  `compactCloseOverhead shape.size`;
- `compactCloseOverhead` is `LittleOLinear`;
- modeled close/LCA query cost is bounded by `compactCloseQueryCost`;
- the returned close position is exact for the Cartesian-shape representative
  RMQ answer when supplied endpoint close positions are exact; and
- payload words read by the directory are bounded by
  `SuccinctRank.machineWordBits shape.bpCode.length`.

The generic macro/micro family theorem is exposed as:

```lean
RMQ.BPNavigation.macroMicroTwoNPlusOBuiltQueryProfile
```

It packages the `2*n + o(n)`, constant-query shape for payload-live BP
close-navigation families.

## Remaining Frontier

The BP navigation spoke is landed as the compact close/LCA layer consumed by
succinct RMQ, plus the basic close/rank bridge. The useful next deepening steps
are:

1. build a fuller tree-navigation facade over balanced parentheses
   (`parent`, `firstChild`, `nextSibling`, subtree intervals, and LCA);
2. route that facade through the public rank/select spoke where possible,
   using `shapeAccessCloseRankProfile` as the first bridge theorem;
3. keep the existing compact close/LCA profile as the RMQ-facing specialization
   rather than forcing every tree-navigation operation through RMQ internals.
