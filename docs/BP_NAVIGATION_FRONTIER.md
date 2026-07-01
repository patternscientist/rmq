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
narrow spoke, but it now exposes the basic charged BP-navigation legs, the first
public subtree-interval operation, and a dense concrete matching-open/enclose
directory over Cartesian-shape balanced-parentheses encodings:

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
- `subtreeIntervalOfInorderFastCosted`: the same subtree interval, but routed
  through a supplied constant-query matching-open component instead of the
  linear excess scan.
- `encloseOpenOfInorderFastCosted`: inorder node index to the enclosing
  parent open position, routed through charged close-select plus a supplied
  constant-query matching-open/enclose component.
- `ConcreteMatchingOpenEncloseDirectory`: a dense concrete table-backed
  component instantiating the matching-open/enclose boundary with constant
  modeled query cost.

It is not yet a complete succinct tree-navigation library.

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
RMQ.BPNavigation.bpPrefixExcess
RMQ.BPNavigation.matchingOpenSearchRef
RMQ.BPNavigation.matchingOpenSearchCosted
RMQ.BPNavigation.matchingOpenSearchRef_some_nearest
RMQ.BPNavigation.matchingOpenOfClose?
RMQ.BPNavigation.matchingOpenOfClose?_nearest_equal_excess_of_bpCloseOfInorder?
RMQ.BPNavigation.subtreeIntervalOfInorder?
RMQ.BPNavigation.subtreeIntervalOfInorderCosted
RMQ.BPNavigation.BalancedParensMatchingOpenAccess
RMQ.BPNavigation.subtreeIntervalOfInorderFastCosted
RMQ.BPNavigation.encloseOpenOfOpen?
RMQ.BPNavigation.encloseOpenOfInorder?
RMQ.BPNavigation.BalancedParensTreeNavigationAccess
RMQ.BPNavigation.encloseOpenOfInorderFastCosted
RMQ.BPNavigation.shapeAccessEncloseOpenProfile
RMQ.BPNavigation.ConcreteMatchingOpenEncloseDirectory
RMQ.BPNavigation.concreteMatchingOpenEncloseDirectory
RMQ.BPNavigation.concreteMatchingOpenAccess
RMQ.BPNavigation.ConcreteMatchingOpenEncloseDirectory.profile
RMQ.BPNavigation.concreteShapeAccessFastSubtreeIntervalProfile
RMQ.BPNavigation.concreteShapeAccessEncloseOpenProfile
RMQ.BPNavigation.singletonLcaCloseSemantics_not_matchingOpen_counterexample
RMQ.BPNavigation.shapeAccessCloseRankProfile
RMQ.BPNavigation.shapeAccessCloseRankExcessProfile
RMQ.BPNavigation.shapeAccessSubtreeIntervalProfile
RMQ.BPNavigation.shapeAccessFastSubtreeIntervalProfile
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

`matchingOpenSearchRef_some_nearest` and
`matchingOpenOfClose?_nearest_equal_excess_of_bpCloseOfInorder?` make the scan
semantics explicit: for a close produced by `bpCloseOfInorder?`, the returned
position is the nearest prefix at or before the close with the post-close
excess, not an arbitrary equal-excess prefix.

The fast subtree profile introduces `BalancedParensMatchingOpenAccess`, a
public constant-query matching-open boundary. `subtreeIntervalOfInorderFastCosted`
consumes that boundary immediately and proves exact agreement with
`subtreeIntervalOfInorder?`, with modeled cost independent of
`shape.bpCode.length`: one close-select, one matching-open query, and two
close-rank queries. The access record separates `payloadBits`, proof-only
exactness, and model query cost.

The next public tree-navigation layer is `BalancedParensTreeNavigationAccess`.
It packages matching-open and enclose-open queries together, with proof-only
exactness fields and a model charge for each tree-navigation query.
`encloseOpenOfInorderFastCosted` consumes that interface immediately: for an
inorder node it finds the node close, asks for the matching open, then asks for
the enclosing open. `shapeAccessEncloseOpenProfile` proves exact agreement with
`encloseOpenOfInorder?` and a cost bound of one close-select plus two
tree-navigation queries.

`ConcreteMatchingOpenEncloseDirectory` is the first concrete instantiation of
that interface. It stores dense `matchingOpenTable` and `encloseOpenTable`
payloads over all BP positions, charges one model tick per table read, and
proves exactness for in-bounds reads in
`ConcreteMatchingOpenEncloseDirectory.profile`. The concrete profiles
`concreteShapeAccessFastSubtreeIntervalProfile` and
`concreteShapeAccessEncloseOpenProfile` consume this directory, so the fast
subtree interval and parent-open/enclose query now have a real constant-query
public component behind them. This is deliberately not a succinct bound:
`concreteMatchingOpenEncloseOverhead shape = 2 * shape.bpCode.length` counts
dense modeled table entries, not an `o(n)` auxiliary payload and not Lean
runtime.

The focused obstruction is
`singletonLcaCloseSemantics_not_matchingOpen_counterexample`: on the one-node
Cartesian shape, singleton LCA-close semantics return the node close, while
matching-open semantics return the opening prefix position. This rules out the
simple reuse of the existing concrete close/LCA query as a matching-open
component.

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
subtree-interval operation. It also has a conditional fast subtree theorem over
a public matching-open boundary, a dense concrete matching-open/enclose
directory, a constant-query parent-open/enclose profile consuming that
directory, and a counterexample showing the current concrete close/LCA query is
not itself the matching-open boundary. The useful next deepening steps are:

1. replace the dense matching-open/enclose table with a payload-live succinct
   directory backed by compact range-min/max or fwd/bwd-search machinery;
2. decide whether public `parent` should return the enclosing open position or
   an inorder parent index, and add the matching-close/select ingredient if the
   latter is required;
3. build the next fuller tree-navigation operations over balanced parentheses
   (`firstChild`, `nextSibling`, and LCA);
4. keep the existing compact close/LCA profile as the RMQ-facing specialization
   rather than forcing every tree-navigation operation through RMQ internals.
