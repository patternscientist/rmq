# Cleanup plan + post-cleanup roadmap

Companion to the elegance/taste audit of `main` @ `59768bd` (see
`AUDIT_AND_A_DESIGN.md`, 2026-06-24 elegance entry). The math is correct and
trust-clean; this document is the plan to bring the *code* up to the standard a
Mathlib/CSLib maintainer would expect, followed by the development steps that
become natural once the cleanup is done.

All line numbers are `main` @ `59768bd`.

## Two live headlines (do not break either)

1. **RMQ capstone** — `2n + o(n)`, `O(1)`, exact succinct RMQ. Lives in
   `SuccinctFinal`; its select path uses the **BP-specialised**
   `SuccinctSelectProposal.RelativeSplitSparseExceptionFalseSelectCloseData` /
   `builtRelativeSplitSparseExceptionFalseSelectCloseData` (SuccinctFinal 707,
   1358–1368).
2. **Rank/select spoke** — `n + o(n)`, `O(1)`, exact bitvector access/rank/select.
   Lives behind `RMQRankSelect`; its select path uses the **generic**
   `GenericSelect.SparseExceptionSelectData` /
   `jacobsonClarkRankSelectFamily`.

**Key finding:** the sparse-exception select algorithm is implemented **twice** —
once BP-specialised (capstone) and once generic (spoke). Unifying them is both
the largest cleanup and the most valuable next development step (see Roadmap §1).

## Invariants every cleanup step must preserve

Run after each step; a step that breaks any of these is reverted:

- `lake build` green (full project).
- `lake env lean scripts/axiom_check.lean`: 477 headliners, trust base
  `{propext, Classical.choice, Quot.sound}`, zero `sorryAx`/`ofReduceBool`.
- `lake env lean scripts/rank_select_axiom_check.lean` clean.
- `scripts/gate.ps1` passes (build + hygiene + native_decide + axiom checks +
  succinct cost/space lints).

Work in small, single-purpose commits so any regression bisects cleanly.

## Cleanup — prioritised (high ROI / low risk first)

### Phase 1 — prune dead/superseded structures  *(highest ROI, lowest risk)*

`rg "^structure .*Select"` = **50** select structures; most are exploration
dead-ends never pruned. Deleting unused code is the safest possible change (the
build fails immediately if something was live).

Confirmed dead islands (referenced only inside `SuccinctSelectProposal`, on
neither live headline path):

- `SparseDenseFalseSelectLocatorEntry` + `FixedWidthSparseDenseFalseSelectLocatorEntryTable`
  and their codec/lemmas (the old locator-entry path; superseded by
  `…DenseLocalEntry`). ~129 internal references — a self-contained subsystem.
- `RelativeSplitRectangularFalseSelectCloseData` (scope-doc Tier 8: superseded).
- `RectangularChargedFalseSelectCloseData` (Tier 8: linear/superseded).
- `SampledPayloadLiveStoredWordSelectData` (+ `…Family`, `ExactSampled…Family`).
- `PayloadBackedStoredWordSelectData`.

Keep (load-bearing): `StoredWordSelectData`, `TwoLevelPayloadLiveStoredWordSelectData`
(capstone), `RelativeSplitSparseExceptionFalseSelectCloseData` (capstone),
`GenericSelect.SparseExceptionSelectData` (spoke), `ChargedSelectPositionSource`,
`RankSelectDirectory`/`RankSelectFamily`, `BitVectorRankSelect*`.

Special case — the `*_not_littleO` / obstruction witnesses (e.g.
`canonicalSelectBlockTablesFinite_identity_payload_not_littleO`): these are
*valuable* honesty artifacts ("this easy route is provably vacuous/linear"). Do
not delete — **move them to `RMQ/Archive/SelectObstructions.lean`** out of the
main import graph, with a header explaining their purpose.

Method: for each candidate, `rg` its name; if every reference is its own
def + immediate lemmas (and nothing on a live path), delete the island and
rebuild. Acceptance: build green, axiom_check unchanged, material line drop.

### Phase 2 — kill dead-history naming

149 `FalseSelect` identifiers live inside the **generic** (`target`-parametric)
builder — the names contradict the code. Plus `built`-prefixed names and 6-noun
pileups up to 58 chars.

- In the `GenericSelect` namespace only, drop `False` from names that are
  target-parametric (`relativeSplitFalseSelectEntryIsMarked` →
  `relativeSplitEntryIsMarked`, etc.) and drop `built` prefixes.
  **Do not** rename the BP-specialised names where `false` is genuine (the
  capstone path) — scope the rename to generic code.
- Shorten noun-pileups by namespacing:
  `sparseDenseFalseSelectDenseLocalEntryMultiwordPayloadBudget` →
  `DenseLocalEntry.payloadBudget`;
  `FixedWidthSparseDenseFalseSelectDenseLocalEntryTable` →
  `DenseLocalEntry.FixedWidthTable` (or `DenseLocalTable`).

Method: one identifier per commit (or a scripted rename + rebuild). Risk:
collisions; the build catches them.

### Phase 3 — split the mega-files

`SuccinctCloseProposal` 26k, `SuccinctSelectProposal` 20k, `GenericSelectBuilder`
6k lines. Mathlib/CSLib split by concept at ~1500.

- `GenericSelectBuilder` → `…/Generic/{Entries,Tables,FlagRank,Directory,Family}.lean`
  (Params and Primitives already separate).
- `SuccinctSelectProposal` → carve out the (now-pruned) BP close-data, the
  primitives, and the Clark parameters into siblings.
- Do it incrementally; watch for import cycles. This is lower risk *after*
  Phase 1 shrinks the files.

### Phase 4 — modernise proof idioms

- **Bool dance** (≈15–37×/file): replace
  `by_cases h : b = true` + `cases h : b · rfl · contradiction` with
  `cases hb : b` at the split (hands you `b = false` directly). Scriptable;
  also consider `Bool.not_eq_true` (unused anywhere today).
- **Centralise reinvented basics** into `RMQ/Core/Prelude.lean` (or
  `NatExtra`/`BoolExtra`): `nat_div_sub_div_le_sub`, `one_lt_two_pow_of_pos`,
  `machineWordBits_le_self_of_pos`, `lt_two_pow_machineWordBits_of_lt`,
  `nat_succ_le_two_pow` — currently buried at SuccinctSelectProposal 8152–8190
  and SuccinctSpace 544.
- **Inline no-op wrappers** (`SparseExceptionSelectData.queryOccurrence
  _data idx := idx`, GenericSelectBuilder 5219).
- **Trim `_profile` boilerplate** (92 such theorems): where a `_profile` is pure
  field-bundling, drop it and let callers project fields, or generate it.

### Phase 5 — the Mathlib / CSLib dependency decision

Root cause of Phases 3–4's reinvention. This is the deferred CSLib-coordination
call (now due post-demo). Options:

- **Take a Mathlib (or CSLib) dependency:** delete the reinvented `Nat`/`Bool`/log
  basics, adopt Mathlib naming + automation (`omega`, `gcongr`, `positivity`,
  `simp` lemmas), shrink the tree substantially. Cost: large dep, slower builds,
  toolchain coupling.
- **Stay Mathlib-free** (for trust/pinning): then at minimum adopt the
  conventions and keep basics in one `Prelude`. Document *why* in the README.

Decide explicitly and record the rationale; everything downstream follows.

## Post-cleanup development roadmap

### 1. Unify capstone select with generic select  *(biggest structural payoff)*

The sparse-exception select is built twice (see "Two live headlines"). Execute
**Tier 7 of `GENERIC_SELECT_REFACTOR_SCOPE.md`**: recover the BP capstone's
select as `GenericSelect.SparseExceptionSelectData (bits := shape.bpCode)
(target := false)`, plus the two BP boundary bridges
(`select_false_bpCode_eq_bpCloseOfInorder?`, `bpCode_rankFalse_full`); then
delete the parallel BP `RelativeSplitSparseExceptionFalseSelectCloseData`
machinery (a large fraction of `SuccinctSelectProposal`). One select
implementation serving both headlines. Gate: capstone theorem name and axiom
profile unchanged.

### 2. Promote the rank/select spoke to a clean public library

It is already standalone (`RMQRankSelect`). Make `RankSelectSpec` *the* public
API, with a short docstring-driven surface and a usage example. Optionally add a
self-imposed non-vacuity guard mirroring
`chargedSelectPositionSource_allows_empty_select_oracle` so the abstract family's
oracle-satisfiability is policed in code, not only in docs.

### 3. New spokes built on rank/select

With a clean rank/select primitive available: wavelet tree, balanced-parentheses
navigation (`findClose`/`enclose`), or range-counting — each reusing the spoke
rather than re-deriving. These are the natural "second succinct structure"
demonstrations.

### 4. Constant-factor research: shared select-0 / select-1

Today `false`/`true` select are two independent directories (2× the select
overhead). Investigate whether one shared structure can serve both targets
(e.g. derive one from the other via rank), removing the constant-factor
doubling. Research-level, not mechanical.

### 5. CSLib contribution path

Once Mathlib-aligned (Phase 5 = "take the dependency"), the bitvector
access/rank/select directory is a natural CSLib contribution. Coordinate
upstream (the previously-deferred item).

## Suggested execution order

Phase 1 (prune) → Phase 2 (rename) → Roadmap §1 (unify capstone select, which
itself deletes more) → Phase 3 (split files, now much smaller) → Phase 4
(idioms) → Phase 5 (dependency decision) → Roadmap §2–5. Phases 1, 2, 4 are
low-risk and can land immediately; §1 and Phase 5 are the strategic moves.
