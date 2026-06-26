# Cleanup Status And Post-Cleanup Roadmap

This note records the cleanup direction after the public RMQ/rank-select
milestones on `main`. It imports the useful conclusion from the external
elegance audits, but it is the current-main plan: do not merge stale audit
branches wholesale.

The theorem content is the asset. The main public-facing cleanup pass is now
complete: the live capstones are stable, stale expedition notes have been
collapsed out of the public summary, archive anchors are separated from the
headline path, and rank/select has a neutral public facade. The remaining items
below are future library-shaping work, not blockers for the current RMQ spoke.

## Live Headlines

Do not break either headline while cleaning.

1. **RMQ capstone.** The public succinct RMQ headline is
   `SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile`:
   exact RMQ, `2*n + o(n)` payload, constant modeled query cost, and the
   two-sided Catalan lower-bound story. The older
   `SuccinctFinal.builtRelativeSplitSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile`
   is no longer the headline path; it remains a checked archive compatibility
   surface for the BP-specialized relative-split path.

2. **Rank/select spoke.** The public bitvector headline is
   `RankSelect.jacobsonClarkNPlusOConstantQuery`,
   exported through `RMQRankSelect`: exact access/rank/select with
   `n + o(n)` payload and constant modeled query cost.

The key structural smell that motivated cleanup was that the sparse-exception
select idea exists in two forms:

- a BP-specialized false-close/select implementation still present as a
  checked compatibility/archive surface through `SuccinctSelectProposal` and
  `SuccinctFinal`;
- a generic `List Bool` implementation consumed by the rank/select spoke
  through `GenericSelect`.

The highest-value cleanup pass made the RMQ capstone consume the generic select
implementation over `bits := shape.bpCode` and `target := false`. The
BP-specialized relative-split path is now explicitly archived as an old
capstone, and its obstruction witnesses live under `RMQ.Archive`. The archive
is now an opt-in root: `import RMQ` no longer imports it, while `import
RMQArchive` / `lake build RMQArchive` keeps those witnesses locally checked.

## Verification Gate

Every cleanup step must preserve the ordinary gate:

```powershell
lake build
lake build RMQHub
lake build RMQRankSelect
lake build RMQArchive
lake env lean scripts\axiom_check.lean
lake env lean scripts\archive_axiom_check.lean
lake env lean scripts\rank_select_axiom_check.lean
rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ RMQHub.lean RMQRankSelect.lean RMQArchive.lean lakefile.toml
rg -n "native_decide|Lean\.ofReduceBool" RMQ RMQHub.lean RMQRankSelect.lean RMQArchive.lean
git diff --check
powershell -ExecutionPolicy Bypass -File scripts\gate.ps1
```

If an obstruction theorem or design-negative theorem is cited by docs after it
is moved, it must remain checked by some import root or explicit script. Do not
turn proved honesty artifacts into dead prose.

## Phase 0: Safety Inventory

Before deleting or moving any source island, run a current-main reference scan.
Older audit branches may be stale.

Classify each candidate as one of:

- **live headline path**: consumed by the RMQ capstone or rank/select spoke;
- **archive-worthy obstruction**: not needed for construction, but valuable
  because it proves a tempting shortcut is vacuous, linear, or insufficient;
- **dead self-contained island**: only referenced by its own definitions and
  immediate lemmas, and not cited by public docs;
- **unsafe or unknown**: defer.

Archive-before-delete is the default for obstruction/prototype artifacts. A
later deletion is fine after the archive import/check policy is explicit.

## Phase 1: Unify RMQ Select With Generic Select

This strategic cleanup target is present in the theorem surface. Keep this
section as the checklist for what the new generic-select capstone discharges
and as the guardrail for follow-up pruning.

The semantic BP bridge facts already exist in `SuccinctSpace`:

- `bpCode_rankFalse_full`;
- `bpCloseOfInorder?_rankFalse_succ`;
- `select_false_bpCode_eq_bpCloseOfInorder?`.

The cleanup target is therefore not to re-prove the BP semantics. It is to make
the final close-access layer consume the generic select source and those
existing bridge facts instead of carrying a parallel BP-specialized select data
structure.

Target shape:

```lean
-- Build the capstone close-access select leg from the generic source.
def genericFalseSelectBPCloseAccessDirectory
    (shape : Cartesian.CartesianShape) :
    ...

theorem genericFalseSelectBPCloseAccessDirectory_profile
    (shape : Cartesian.CartesianShape) :
    ...

-- Capstone theorem retains the public profile and axiom story.
theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile :
    ...
```

The exact theorem names may change to match existing namespaces, but the
adapter must discharge:

- select exactness: generic `select false shape.bpCode` agrees with
  `bpCloseOfInorder?`, using the existing `SuccinctSpace` theorem;
- rank exactness: generic/BP rank-close agrees with the close-rank facts already
  used by `SuccinctFinal`;
- payload accounting: the generic select auxiliary payload is counted once, not
  duplicated beside the old BP-specialized payload;
- query-cost accounting: the existing capstone cost stays constant under the
  same RAM/indexed-read model;
- theorem consumption: the final RMQ capstone consumes the generic select path,
  not a parallel BP-specialized path.

The generic select source is now the concrete source consumed by
`SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile`,
with total and two-sided wrappers. The old relative-split capstone is no
longer part of the main load-bearing axiom inventory, but it remains checked
through the archive namespace/script until a later source-prune pass.

## Phase 2: Archive Or Prune Superseded Select Code

After Phase 1, rerun the Phase 0 inventory. Then:

- move proved obstruction/no-go results to an explicit archive module such as
  `RMQ/Archive/SelectCompatibility.lean`;
- keep that archive checked if public docs cite those results;
- delete genuinely dead self-contained islands only after a green gate;
- avoid deleting old code merely because it is ugly if it still carries a
  distinct theorem not reproduced by the generic path.

This is where candidates such as old locator-entry tables, rectangular select
experiments, and sampled wrapper variants should be reclassified on current
main. Do not trust stale line counts or stale reference counts.

The first archive boundary is now active: old BP-specialized sparse/dense and
relative-split select/access checks have moved from the main curated axiom
inventory to `scripts/archive_axiom_check.lean`, with obstruction anchors in
`RMQ/Archive/SelectObstructions.lean`, the old BP-specialized capstone alias in
`RMQ/Archive/BPSpecializedCapstone.lean`, and compatibility names in
`RMQ/Archive/SelectCompatibility.lean`. `RMQArchive` is the explicit import root
for that code, and `scripts/gate.ps1` builds it and runs the archive check.
Source declarations are deliberately still present. Treat direct deletion or
deeper physical source extraction as a later proof-heavy pass, after another
reference scan confirms that no live generic capstone or rank/select theorem
consumes the candidate.

The first real prune pass narrowed that archive to retained witnesses: the old
sparse/dense obstruction theorems and the old relative-split total two-sided
capstone. Intermediate sparse/dense prototype profiles are no longer archive
anchors, and the dead `SuccinctFinal` sparse/dense close-access adapter was
removed.

The first physical source prune has now removed the self-contained rectangular
local/super generated-entry rows, their row-specific obstruction lemmas, the
`RelativeSplitRectangularFalseSelectCloseData` island, and its padded-local
no-go theorem. A follow-up prune removed the old four-field
`SparseDenseFalseSelectCloseData` locator surface itself, retired the
locator-specific archive aliases, and kept only the smaller shared-locator
obstruction witnesses in `RMQ/Archive/SelectObstructions.lean`. The later
cleanup pass also retired the stale `RectangularChargedFalseSelect...`
compatibility names; the live finite-block-table obstruction route is now named
only by the clearer `TwoLevelFalseSelect...` surface.

Decision: keep the remaining BP-specialized relative-split capstone
intentionally as an old capstone, not as a public headline. The archive split
has started: retained obstruction witnesses now live in
`RMQ/Archive/SelectObstructions.lean`, the old capstone alias lives in
`RMQ/Archive/BPSpecializedCapstone.lean`, and
`RMQ/Archive/SelectCompatibility.lean` is only a compatibility import/alias
root. A later proof-heavy source split can physically move the old
relative-split construction out of `SuccinctFinal`; it should not be deleted
unless the old capstone is deliberately retired.

## Phase 3: Split Mega-Modules

The archive split has begun. The next proof-module splits should proceed by
concept:

- `GenericSelectBuilder` into entries/tables/flag-rank/directory/family pieces;
- BP close/navigation code into local, fringe, interior, close/LCA, and RMQ
  adapter pieces;
- archive modules for obstruction results and failed routes.

Read-only comparison against Mathlib/CSLib/AFP/refinement-framework norms points
to the same priority order: split by dependency role, keep public facades thin
and citable, and make archive code optional or physically separate once the old
witnesses no longer need to live inside the main implementation modules.

The first generic-select physical split is active:

- `RMQ/Core/GenericSelect.lean` is the target-parametric select builder root;
- `RMQ/Core/GenericSelect/LowLevel.lean` is a compatibility barrel over the
  low-level role modules below;
- `RMQ/Core/GenericSelect/SelectFacts.lean` owns neutral select/rank facts such
  as select monotonicity and rank-prefix/select-existence lemmas;
- `RMQ/Core/GenericSelect/Arithmetic.lean` owns shape-free arithmetic,
  machine-word growth lemmas, and generic sparse/dense overhead budgets;
- `RMQ/Core/GenericSelect/DenseEntryTable.lean` owns fixed-width dense-local
  entry tables and entry-based slot arithmetic;
- `RMQ/Core/GenericSelect/DenseWord.lean` owns aligned payload-word helpers for
  dense two-word select;
- `RMQ/Core/GenericSelect/RelativeSplit.lean` owns relative-split slot and
  base-position helpers;
- `RMQ/Core/GenericSelect/LegacyNames.lean` quarantines older false-named
  aliases for compatibility; new generic code should use neutral names;
- `RMQ/Core/GenericSelect/Params.lean` owns the Clark-style length parameters
  and generic overhead budget;
- `RMQ/Core/GenericSelect/Primitives.lean` owns the target-threaded dense
  two-word decode primitive and payload-routing certificates;
- `RMQ/Core/GenericSelect/PrimitiveLegacyNames.lean` quarantines the older
  false-named primitive wrapper aliases for compatibility;
- `RMQ/Core/GenericSelect/Slots.lean` owns occurrence counts, slot arithmetic,
  span classification, and sparse-exception counting;
- `RMQ/Core/GenericSelect/Entries.lean` owns super/local entry construction and
  classification flag vectors;
- `RMQ/Core/GenericSelect/FlagRank.lean` owns the generic two-level flag-rank
  directory and its payload budget;
- `RMQ/Core/GenericSelect/RelativeTables.lean` owns relative-offset tables,
  fixed-width dense-local entry tables, width bounds, and payload bounds;
- `RMQ/Core/GenericSelect/Tables.lean` is now only a compatibility barrel for
  the three table-layer modules above;
- `RMQ/Core/GenericSelect/Directory.lean` owns the payload-live
  sparse-exception directory and charged directory read profile;
- `RMQ/Core/GenericSelect/SelectSource.lean` owns the neutral
  `ChargedSelectPositionSource` interface shared by proposal and generic-select
  layers;
- `RMQ/Core/GenericSelect/Source.lean` owns `SparseExceptionSelectData`, exact
  `selectCosted`, and the `ChargedSelectPositionSource` adapter;
- `RMQ/Core/GenericSelect/Family.lean` owns the Jacobson/Clark
  `RankSelectSpec` adapter and public family profile;
- `RMQ/Core/GenericSelect/BPCompat.lean` and
  `RMQ/Core/GenericSelectBPCompat.lean` own/export the small `shape.bpCode`,
  `target := false` bridge facts that should not live in the plain bitvector
  core;
- `RMQ/Core/GenericSelectLegacy.lean` is the terminal compatibility root for
  legacy false-named aliases; the canonical generic root does not import it;
- `RMQ/Core/SuccinctRankSelect.lean` is the construction-level bitvector
  rank/select root;
- `RMQ/Core/BPCloseNavigation.lean` is the compact BP close/LCA navigation root;
- `RMQ/Core/SuccinctRMQ.lean` is the final succinct-RMQ root.

`RMQ/Core/GenericSelectBuilder.lean`, `RMQ/Core/GenericSelectParams.lean`, and
`RMQ/Core/GenericSelectPrimitives.lean` remain as compatibility import barrels
for old downstream imports. New construction imports should prefer
`RMQ.Core.GenericSelect` or the narrower split modules under
`RMQ.Core.GenericSelect.*`. Public aliases stay terminal in
`RMQ.Core.RankSelectPublic` and `RMQRankSelect`.

The generic-select dependency inversion is now active: canonical generic modules
no longer import `SuccinctSelectProposal` for neutral low-level arithmetic,
dense-entry, fixed-width-table, or relative-split helpers. Those helpers live
under the `GenericSelect.LowLevel` barrel and its role modules, while
BP-shaped bridges remain above the plain bitvector core in
`GenericSelect.BPCompat`, `GenericSelectBPCompat`, `SuccinctSelectProposal`,
and `SuccinctFinal`. The canonical `RMQ.Core.GenericSelect` root is pure
plain-bitvector generic; it does not import BP compatibility or legacy aliases.

The select-side proposal layer has started the same dependency-role split.
`RMQ/Core/SuccinctSelect.lean` is a thin reusable barrel for
`SuccinctSelect/TwoLevel.lean`, `SuccinctSelect/Obstructions.lean`, and
`SuccinctSelect/DenseLocalTables.lean`. The historical
`RMQ.SuccinctSelectProposal` namespace is preserved, while
`RMQ/Core/SuccinctSelectProposal.lean` now owns the remaining C1-specific
sparse/dense relative-split false-close construction.

The close-navigation proposal is also split by role.
`RMQ/Core/SuccinctClose.lean` is the thin reusable barrel for
`SuccinctClose/BlockLocal.lean`, `SuccinctClose/RangeSummary.lean`,
`SuccinctClose/RelativeSummary.lean`, `SuccinctClose/RangeWitness.lean`,
the `SuccinctClose/EndpointFringe/*` prefix-range, interior-candidate, and
endpoint-macro layers, with the endpoint macro itself split into range-macro
and micro-codebook layers. The relative-rmM macro is likewise split behind
`SuccinctClose/RelativeRmmMacro.lean` into abstract macro, endpoint codebook,
compact endpoint, local BP decoder, concrete directory, and macro/micro family
layers. `RMQ/Core/SuccinctCloseProposal.lean` is now a compatibility import
root for the historical proposal name.

Keep import direction simple:

```text
bitvector spec -> generic rank/select builders -> BP navigation -> RMQ capstone
```

Generic bitvector code should not depend on Cartesian/RMQ concepts; BP/RMQ
bridges should live above the generic core in compatibility modules.

Archive code is an optional import root for downstream users, but it is still
checked by the full repository gate. In other words, `import RMQ` does not pull
archive witnesses in, while `scripts/gate.ps1` still builds `RMQArchive` so the
archived witnesses do not silently rot.

If the archive should be kept locally but removed from a public repository, the
safe version is: move those files under an ignored local-only directory, remove
`RMQArchive` and archive axiom checks from the public Lake/gate surface, and
remove or rephrase public docs that cite archive theorem names. Do not keep
public docs or gates that depend on ignored local files.

## Naming And Proof Idioms

Completed:

- Short public aliases for the main theorem surfaces now live in
  `RMQ/Headlines.lean`; keep adding aliases there when a public-facing name is
  useful, while preserving the original construction-heavy declaration names.
- `RMQ/Core/RankSelectPublic.lean` exposes neutral `RMQ.RankSelect.*` names for
  the standalone rank/select spoke.
- Compatibility aliases for archive-facing old names remain in
  `RMQ/Archive/SelectCompatibility.lean`.

Future opportunistic work:

- In generic select code, remove `False` from names that are truly
  target-parametric.
- Centralize repeated Nat/Bool/log facts in a small local prelude if the repo
  stays Mathlib-free.
- Refactor repeated Bool case-split boilerplate and giant arithmetic proof
  fragments opportunistically, not as a broad risky rewrite.

## Dependency Decision

The project is still Mathlib-free by default. That remains a legitimate choice,
but the cleanup phase should make the tradeoff explicit:

- staying Mathlib-free means keeping a small local prelude and accepting some
  arithmetic verbosity;
- taking Mathlib or CSLib later could shrink proof boilerplate and align names
  with broader Lean CS infrastructure, but would change build/trust/project
  constraints.

No cleanup task should introduce Mathlib without an explicit user decision.

## Post-Cleanup Development

After the select unification and module cleanup, the natural next spokes are:

1. examples and stable user-facing docs for the public rank/select package;
2. balanced-parentheses navigation over the public rank/select surface;
3. wavelet trees or range counting as the next CS166-style succinct structure;
4. compressed/FID-style rank/select space refinements such as
   `log2 (Nat.choose U m) + o(U)` under an explicit model;
5. possible CSLib contribution once the API is stable enough to be useful
   outside this repo.
