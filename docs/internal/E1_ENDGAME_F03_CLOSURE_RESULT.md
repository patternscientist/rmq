# EG-CP-F03 geometry closure — result

Coordinator: C06 (Claude runtime). Date: 2026-07-26.
Governed base: `d988166` (`origin/main`).
Row: `EG-CP-F03-GEOMETRY-CLOSURE`, `docs/internal/RMQ_ENDGAME_ROADMAP.md:374`.

Supersedes the residual in
`docs/internal/E1_ENDGAME_F03_GEOMETRY_CLOSURE_CAMPAIGN.md` section 5 and the
T1 record in `docs/internal/E1_ENDGAME_T1_SELECT_LEAF_RESULT.md`.

**This record accepts no theorem and makes no public claim.** Acceptance of a
Stage F row is a coordinator act taken against the frozen matrix; this document
reports what is now proved and in-tree, and states precisely what the row's own
minimum-evidence clause still asks for.

---

## 1. What is proved and in-tree

New module `RMQ/Core/SuccinctFinal/RAM/GeometryClosure.lean` (81 declarations),
reachable from the root library via one added import in `RMQ.lean:52`.

The capstone, i.e. the literal row requirement:

```lean
theorem T4_wholeQuery_trace_size_only {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) (store : WordRAM.ReadStore) (l r : Nat) :
    SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore a store l r
      = SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore b store l r
```

Full `TraceResult` equality — identical ordered event list **and** identical
value. No size threshold, no regime restriction.

The public entry, over input lists:

```lean
theorem queryTraceResultWithStore_size_only (xs ys : List Int)
    (store : WordRAM.ReadStore) (l r : Nat) (h : xs.length = ys.length) :
    SuccinctClassic.queryTraceResultWithStore xs store l r
      = SuccinctClassic.queryTraceResultWithStore ys store l r
```

and the **positive** form, with a witness function that mentions no input list:

```lean
def publicQueryOfLength (n : Nat) (store : WordRAM.ReadStore) (l r : Nat) := ...
theorem queryTraceResultWithStore_factors (xs : List Int) (store) (l r) :
    SuccinctClassic.queryTraceResultWithStore xs store l r
      = publicQueryOfLength xs.length store l r
```

Per-leaf, all universal and unconditional: `SelectLeaf.L1_route_shape_size_only`
(L1, select-close), `L2_route_size_only` (L2, LCA-close, **both** arms),
`L3_rankClose_size_only` (L3, rank-close), plus `offsets_congr` and
`interiorRangeMinComputation_congr` (the interior cone, campaign obligation T3),
`wholeQueryInstr_congr` and `wholeQueryProgram_congr` (the evaluator).

Axioms on every final: `[propext, Classical.choice, Quot.sound]`;
`validRange_congr` depends on none. No `sorryAx`, no `native_decide`, no
`ofReduceBool`, no `axiom`, no `opaque`, no `implemented_by`.

`lake build RMQ` completes successfully, 261 targets, with the module built as
`[259/261]`. Verified by the coordinator, and independently by two agents who
each restored the build worktree afterwards.

---

## 2. Why this discharges the row, and how it differs from what was asked

The row's requirement is that *every* data-dependent offset, length, branch,
divisor and table selector factors through `n`, the endpoints, header words and
prior probes. `T4_wholeQuery_trace_size_only` establishes exactly that, by
contraposition over the whole executed surface: if any such value failed to
factor through the allowed inputs, it would depend on shape content beyond
`size`, and there would exist two equal-size shapes, a store and endpoints on
which the executed program issued a different address, took a different branch,
or produced a different value. The theorem says no such triple exists.

**This is strictly stronger than the inventory the row's evidence column
describes**, and it is stronger in the exact way the campaign needed. An
inventory of 55 constants proves the same thing only if the enumeration is
complete *and* every per-item argument is valid. The campaign's inventory failed
both halves — 39 content-dependent constants were invisible to the instrument,
and its syntactic test had a false-clean mode refuted by
`bpBlockArgMinPrefixPosFrom` (campaign section 3.1). T4 needs neither.

**What the row asked for that this is not.** The evidence column says
"exhaustive typed inventory ... and universal consumers". `wholeQueryProgram_congr`
is a universal consumer in the literal sense — quantified over all programs and
all states — but no *inventory artifact* was produced. Whether a theorem that
subsumes the inventory satisfies a clause that names the inventory is an owner
call, not a coordinator one. It is recorded here rather than assumed away.

---

## 3. Scope fence — load-bearing, not cosmetic

The theorems are about the **supplied-store** surface. The store-free surface
`SuccinctClassic.queryTraceResult` / `queryCosted` is genuinely and measurably
content-dependent: two length-10 lists give 96 events / cost 96 versus 79 events
/ cost 79.

That is **not** a violation. Different content builds a different memory image,
which returns different probe replies, which legitimately produces different
addresses — the row's allowed inputs explicitly include "prior probes". It does
mean that **no claim derived from this module may be phrased over "the public
query" without "at a shared supplied store"**, and the cost claim in
`RMQ/Headlines/` is stated over the store-free surface.

A control confirms the fence is real: feeding the store-free route to
`queryTraceResultWithStore_size_only` fails to typecheck.

---

## 4. Anti-vacuity

A size-only theorem about a controller that reads nothing would be worthless.
Executed evidence that it reads, and that the shape argument is not a phantom:

- **`rfl`-must-fail controls.** The same four statements with the length/size
  hypothesis dropped are offered to `rfl`; **all four fail**. The L2 congruence
  at two distinct shapes deterministically times out in `isDefEq`. None of these
  congruences is a definitional triviality.
- **Hypothesis cannot be smuggled.** Instantiating the capstone with `rfl` at
  arbitrary `a b` is a type mismatch.
- **The controller genuinely reads.** Running the controller on one list's
  Cartesian shape against *another* list's store returns **the store owner's
  answer**, not the shape owner's. Output comes from probe replies.
- **Both L2 arms are live and covered.** At n = 10 the block size is 8; closes
  `(1,17)` land in blocks `(0,2)` — cross-block, 41 events — while `(1,3)` land
  in block `(0,0)` — same-block, 13 events. `L2_lcaClose_size_only` does
  `by_cases` on the branch predicate and discharges the arms separately.
- **Witnesses are genuinely distinct.** `node (node empty empty) empty` versus
  `node empty (node empty empty)`: equal `size`, different `bpCode`, both proved
  with **no axioms at all**. At the public entry, `[3,1,2,0]` and `[0,2,1,3]`
  have equal length and provably different Cartesian shapes.
- **Expected-type pins** written from the row text rather than from the proofs,
  each inhabited by the theorem *value* alone, by three parties independently
  (the capstone lane, the adversary, and the coordinator).
- **Chain integrity.** `rfl` proofs pin public entry → guard → `cartesianShape`
  → top level → evaluator → instruction → each leaf, including that the
  controller really is the five-instruction program. No sibling substitution.

---

## 5. What remains

**Inside F03's scope: nothing mathematical.** Every obligation in the campaign's
section 5.2 that F03 owns — T1, T3, T4 and the Tier-0 port — is discharged.

**Recorded as remaining, and not claimed as closed:**

1. **The inventory artifact** (section 2 above). Owner call.
2. **Probe counting is `EG-CP-F08`'s row, not this one.** The row texts are
   explicit: F03 covers offsets, lengths, branches, divisors and table selectors;
   the `n`-independent cap lives in `EG-CP-F08-PHYSICAL-CODEC-AND-CAP`
   (`RMQ_ENDGAME_ROADMAP.md:379`). Measured for F08's benefit: the canonical
   weighted cost rises from 45 at n = 1 to 118 at n = 32 against the frozen bound
   of 210, over a small sample of three shapes and five endpoint pairs per size.
   The bound is a proved theorem, so growth is bounded; but a *physical* cap must
   be derived from the packed trace, cell crossings can cost two probes, and the
   roadmap's allowance that the cap "may equal `210` plus descriptor/packing
   overhead, or another constant" looks well-founded.
3. **"Header words" are not separately identified** in these theorems — they are
   subsumed under the supplied store. `EG-CP-F01`/`F02` own the header schema,
   for which the campaign derived K = 1 (the field `n`, width
   `w(n) = ⌊log₂ 2n⌋ + 1`), with a K = 3 branch depending on whether F01 pads two
   select regions to their existing `n`-only budgets.
4. The campaign's other section 5.1 process gaps are untouched by this delta.
