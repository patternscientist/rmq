# Balanced-Parentheses Navigation Spoke

Snapshot: 2026-07-01. This note records the extracted public surface for the
compact balanced-parentheses close/LCA navigation layer used by the succinct
RMQ capstone, plus the first public tree-navigation bridge over BP
rank/select.

## Import

Use the standalone import root:

```lean
import RMQBPNavigation
```

`RMQBPNavigation` exposes neutral names under `RMQ.BPNavigation`. It is still a
narrow spoke, but it now exposes the basic charged BP-navigation legs and the
first public subtree-interval operation over Cartesian-shape
balanced-parentheses encodings:

- `closeOfInorderCosted`: inorder node index to closing parenthesis, routed
  through false-select;
- `inorderOfCloseCosted`: closing parenthesis to inorder node index, routed
  through false-rank at `close + 1`.
- `excessAtCosted`: prefix excess routed through charged open/close rank
  queries; and
- `closeExcessOfInorderCosted`: inorder node index to
  `(close position, excess after close)`, routed through the public close leg
  plus `excessAtCosted`.
- `subtreeIntervalOfInorderCosted`: inorder node index to a half-open inorder
  subtree interval, routed through charged close-select, a charged excess scan
  for the matching open, and two charged close-rank queries.

It is not yet a complete tree-navigation library.

Verification:

```powershell
lake build RMQBPNavigation
lake env lean scripts/bp_navigation_axiom_check.lean
```

## Public Surface

The rank/select-backed BP navigation and first tree-navigation bridge are
exposed as:

```lean
RMQ.BPNavigation.BalancedParensAccess
RMQ.BPNavigation.closeOfInorderCosted
RMQ.BPNavigation.inorderOfCloseCosted
RMQ.BPNavigation.excessAtCosted
RMQ.BPNavigation.closeExcessOfInorderCosted
RMQ.BPNavigation.matchingOpenSearchRef
RMQ.BPNavigation.matchingOpenSearchCosted
RMQ.BPNavigation.matchingOpenOfClose?
RMQ.BPNavigation.subtreeIntervalOfInorder?
RMQ.BPNavigation.subtreeIntervalOfInorderCosted
RMQ.BPNavigation.shapeAccessCloseRankProfile
RMQ.BPNavigation.shapeAccessCloseRankExcessProfile
RMQ.BPNavigation.shapeAccessSubtreeIntervalProfile
```

The first bridge profile proves one-query modeled cost for both close/rank
directions, exact agreement with `SuccinctSpace.bpCloseOfInorder?`, and exact
recovery of the inorder index when the supplied close position comes from
`bpCloseOfInorder?`. The stronger excess profile adds charged prefix-excess
queries, the balanced-parentheses close-rank/open-rank invariant, and exact
close-plus-post-close-excess recovery for an inorder node with cost bounded by
one close select plus two rank queries. The erased theorem
`RMQ.BPNavigation.closeRankPrefix_le_openRankPrefix_of_le` exposes that same
balanced-prefix fact directly over `rankPrefix`.

The subtree-interval profile is the first public BP tree-navigation operation
rather than another close/excess adapter. Its reference semantics
`subtreeIntervalOfInorder?` use the existing inorder close lookup plus a
rank/excess matching-open search; its costed query
`subtreeIntervalOfInorderCosted` performs exactly that search through charged
public excess queries and then reads the interval endpoints with charged
close-rank queries. `subtreeIntervalQueryCost` is a coarse model-level budget:
one close select, one post-close excess query, at most one excess query per BP
position in the scan window, and two close-rank queries. It is not a payload-bit
bound and not a Lean evaluator runtime claim.

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
succinct RMQ, plus the close/rank/excess bridge and the first charged public
subtree-interval operation. The useful next deepening steps are:

1. build the next fuller tree-navigation operations over balanced parentheses
   (`parent`/`enclose`, `firstChild`, `nextSibling`, and LCA);
2. replace the linear charged matching-open scan with a reusable constant-query
   enclose/matching-open directory when that directory is exposed through the
   public rank/select/BP boundary;
3. keep the existing compact close/LCA profile as the RMQ-facing specialization
   rather than forcing every tree-navigation operation through RMQ internals.
