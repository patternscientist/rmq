# RMQ Proof Digestion Map

Snapshot: 2026-06-28. This is the index for the classroom-facing digestion
layer. The detailed notes are split by proof frontier so each handout can be
read aloud without carrying the whole theorem inventory.

The standard is the "proof digestion" framing from the supplied Tao talk
transcript: a checked proof is not fully useful until a mathematically mature
reader can say what changed, what it means, what assumptions are live, and what
questions remain.

## Reading Order

- [`PROJECT_STATE_2026_06_28.md`](PROJECT_STATE_2026_06_28.md): current
  project-wide digest after the rank/select route-metadata and union-find
  rank-slack milestones, including the merged rank/select primary-budget /
  split-width route-directory work and union-find Tarjan-level scaffold.
- [`RMQ_CAPSTONE.md`](RMQ_CAPSTONE.md): the stable RMQ theorem story, including
  Cartesian shape, the Catalan lower bound, BP payload, modeled query cost, and
  the anti-oracle checks on the final query path.
- [`RANK_SELECT_FID_FRONTIER.md`](RANK_SELECT_FID_FRONTIER.md): the rank/select
  spoke after the chunk-route milestone, including fixed-weight codes,
  sentinel chunks, access/rank/select routes, route/class-length metadata,
  charged reads, narrow metadata accounting, the log-chunk primary block-code
  budget bridge, and the split-width table/RAM repair.
- [`UNION_FIND_AMORTIZATION_FRONTIER.md`](UNION_FIND_AMORTIZATION_FRONTIER.md):
  the union-find spoke after the rank-bucket, rank-slack, Tarjan-level,
  phase-count, and level-index scaffold milestones, and why inverse-Ackermann
  accounting is still open.

## Public Entry Points

```lean
import RMQ              -- RMQ/LCA family and public headline aliases
import RMQHub           -- reusable cost, RAM, refinement, table, lower-bound hub
import RMQRankSelect    -- standalone plain-bitvector rank/select spoke
import RMQBPNavigation  -- balanced-parentheses close-navigation spoke
import RMQUnionFind     -- union-find specification and forest-refinement spoke
import VerifiedDS       -- thin aggregate facade over the active public roots
```

The broadest facade is `VerifiedDS.lean`, but the citable theorem names remain
under the older roots. For a public talk, start with `RMQ.Headlines` for RMQ
and rank/select headlines, then use `RMQRankSelect`, `RMQBPNavigation`, and
`RMQUnionFind` for the active spokes.

## Common Assumptions Ledger

| Category | What it means | What not to say |
| --- | --- | --- |
| Payload bits | Serialized modeled state bits such as BP shape bits, rank/select directory bits, route tables, fixed-weight codes, and explicitly counted stores. | Do not count Lean proof certificates as stored bits unless a theorem serializes them. |
| Proof-only fields | Invariants, exactness certificates, and refinement proofs used to make Lean accept the construction. | Do not treat them as executable data by default. |
| Modeled cost | Natural-number costs in `Costed` or primitive traces in `RAM.Exec`; indexed reads and bounded word primitives are unit-cost under the model. | Do not claim Lean `List` runtime is constant time. |
| Import roots | Public roots are stable reader entry points. | Do not infer that `VerifiedDS` is a namespace migration; it is only an aggregate facade. |

