# EG-CP-F03 campaign evidence — UNVETTED working artifacts

Preserved 2026-07-26 from the F03 geometry-closure campaign's session-scoped
working directory, at governed base `d09bed7`. Scope is the campaign window
only; pre-campaign scratch files from unrelated E1 work were deliberately
excluded.

**These are not acceptance evidence.** They have not been reviewed
declaration-by-declaration by the coordinator, they are not part of any build
target, and no claim in the project may cite them as established. They are kept
because a prior failure mode here was exactly a strong claim with no branch, no
commit and no replay: the theorem names in the residual surface are recoverable
from these files, and a porting worker should start here rather than re-derive.

Read `../E1_ENDGAME_F03_GEOMETRY_CLOSURE_CAMPAIGN.md` first. It states what is
established, what was refuted (including the coordinator's own instrument), and
what remains.

## How to run one

These import the RMQ library and are executed, not built:

    cd <a worktree with a complete .lake build at this commit>
    lake env lean docs/internal/f03_evidence/<file>.lean

`lake env lean` does not rebuild. A run costs a few seconds once imports are
warm. Files ending `_out.txt` or `_log.txt` are captured output from the
correspondingly named `.lean` file.

## Coordinator-authored instruments

| file | what it does |
|---|---|
| `f03_inventory.lean` | Full transitive constant closure; first-pass buckets. |
| `f03_inventory2.lean` | Computational core (values only, theorems skipped) plus the `bpCode`-under-`List.length` test. **The report records this test's false-clean failure mode; do not reuse it as a taint analysis.** |
| `f03_channels.lean` | The eliminator cut that makes `bpCode`/`size` the complete content channel. |
| `f03_regimes.lean` | Regime map: geometry values across structurally extreme same-size shapes, n = 0..1024. |
| `f03_select_leaf.lean` | Leaves L1/L3 across extreme same-size shapes. |
| `f03_lca_leaf.lean`, `f03_lca_min.lean` | Leaf L2; superlinear in the interpreter, hence the evaluation ceiling recorded in the report. |
| `f03_superlong.lean` | The `cliff` family, built to move `superSpan`; select transcripts across it. |
| `f03_longflag.lean` | The `superIsLong` crossover scan and the segment evidence (9/10/11/12). |
| `f03_crossshape.lean`, `f03_crossshape2.lean`, `f03_theorem_probe.lean`, `f03_active_regime.lean` | Cross-shape transcript experiments. Note the regime ceiling in the report before citing any of these. |
| `F03_COORDINATOR_FINDINGS.md` | Running coordinator notes during the campaign, superseded by the report. |

All other files are agent-authored working artifacts from the 30-agent campaign,
prefixed by lane (`adv*`, `advQ*`, `dp_*`, `qz_*`, `wq_*`, …).
