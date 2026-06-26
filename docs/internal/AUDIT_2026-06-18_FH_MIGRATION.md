# RMQ POC Audit — Fischer-Heun microtable migration completed

Date: 2026-06-18 (round following the unwired-migration stop logged in
`AUDIT_AND_A_DESIGN.md`).

Staging note: audit-branch record. Codex's working-tree `ROADMAP.md` /
`CODEX_AUTONOMY.md` are the canonical steering docs; status updates implied here
should land there.

## Scope

Full working-tree development: 33 Lean modules (20 `Core/`, 13 `Impl/`) +
`scripts/axiom_check.lean`, aggregated by `RMQ.lean` (all imported, no orphans).

## Health

- `lake build`: green.
- Hygiene: no `sorry`/`admit`/`axiom`/`native_decide`/`partial`/`extern`/`noncomputable`.
- Trust base: curated headline theorems depend only on
  `{propext, Classical.choice, Quot.sound}` (several fewer); `0` `sorryAx` /
  `ofReduceBool` hits.

## Verdict

This round is the clean completion of the Fischer-Heun boundary-microtable
migration that the previous round left as unwired scaffolding. Every concern
from the prior round-log entry is resolved, and **target B is now substantively
closed**: there are two genuinely fully-derived `Core.Refine.StoredMatrix`
instances (the sparse table and Fischer-Heun), the asserted microtable cost is
retired, and FH's value-correctness is unconditional for built states. No filler,
no dead code, debt reduced.

## Evidence

- **Asserted path retired, not bypassed.** `materializedMicrotableLookupCost`
  occurrences in `Impl/FischerHeun.lean`: **9 → 0**. The asserted
  `localBlockCandidateCosted` definition is deleted; only the traced
  `storedLocalBlockCandidateCosted` (backed by `storedMicrotableForInput`)
  remains.
- **Traced path wired into the live query.** `queryWithStateCosted` routes
  boundary candidates through the stored/traced path. Cost bound **11 → 13**
  (`queryWithStateCosted_cost_le_thirteen_of_blockSize_pos`); honest
  re-accounting (real microtable reads counted, not a single asserted tick).
  LCA propagated **14 → 16** (`canonicalConcreteQueryCosted_cost_le_sixteen_of_large`).
- **Correctness unconditional for built states.**
  `buildWithBlockSize_summaryTableRefines` (FischerHeun.lean:471) discharges the
  refinement hypothesis; `queryWithStateCosted_value_built`
  (FischerHeun.lean:1140, `@[simp]`, no hypotheses) yields an unconditional
  `queryCosted_value` (1186) refining the verified query. The `_of_lt`
  microtable in-bounds obligations are discharged internally from query
  validity, not leaked into the query's correctness.
- **Backend intact.** `query_sound` / `query_complete` / `invalid_none`
  (1473 / 1479 / 1485) hold via the unchanged value-level `queryWithState`.
- **Supporting refinement infra is consumed, not dead.** New
  `Refine.StoredMatrix.cell?_eq_absCell?` / `row?_getD_toList_eq_absRow?_getD` /
  `cell?_getD_eq_absCell?_getD` and `SparseTable.Instrumented.tableRowArray_value_toList_of_stored`
  are exactly the cell-access refinement lemmas the wiring required.

## Residuals

1. **Cosmetic — formal B closure.** No single bundled capstone
   `fischerHeun_refines_with_steps` (unconditional value-refinement ∧ derived
   steps ≤ 13) is stated or registered in `scripts/axiom_check.lean`. Both halves
   exist (`queryCosted_value` + `queryWithStateCosted_built_cost_le_thirteen_of_large`);
   compose and register them to make the closure legible.
2. **A's standing ceiling.** Escape hatch closed (prior round) and FH now on the
   traced cost model (this round), so A is materially advanced — but value-side
   `List` plumbing in the build path is still the probe-count vs full-machine-step
   residual. That remains A's last item.

## A–D scorecard

| Target | Status |
|---|---|
| **A** machine-step cost model | Materially advanced. Escape hatch closed; sparse **and** FH on traced/derived cost. Residual: count remaining value-side plumbing (probe-count → full machine-step). |
| **B** refinement framework + 2 instances | Substantively done — two fully-derived instances (sparse + FH), asserted microtable retired, correctness unconditional. Cosmetic residual: bundle + register the capstone. |
| **C** lower-bound framework + RMQ instance | Done. |
| **D** one research headline | LCA correctness done; cost derived but still gated (`_of_firstOccurrences` / supplied first-occurrence). D-LCA (costed first-occurrence build, unconditional) is the main open headline. |

POC finish line (A + B + C + one of D): **C done, B done modulo the cosmetic
capstone, A nearly there, D-LCA the main remaining target.**

## Recommended next run

1. State + register the FH capstone to formally close B.
2. Then D-LCA: cost the first-occurrence (and node/depth) table build so the LCA
   bound drops its `_of_firstOccurrences` / supplied hypotheses and becomes a
   single build-plus-query theorem that consumes its own built state.
   (Alternatively, close A's plumbing residual first if finishing the cost model
   is preferred; D-LCA is the more headline-moving.)
