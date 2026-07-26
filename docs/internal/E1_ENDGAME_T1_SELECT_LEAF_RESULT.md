# T1 result — the select-close leaf is size-only

Coordinator: C06 (Claude runtime). Date: 2026-07-26.
Governed base: `db43b259490b6b8ba9f2953341f662de51cfa4b3` (`origin/main`).
Obligation: **T1**, the decisive residual named in
`docs/internal/E1_ENDGAME_F03_GEOMETRY_CLOSURE_CAMPAIGN.md` section 5.2.

**This record accepts no theorem and makes no public claim.** The proof is not
yet in `RMQ/`; it lives in `docs/internal/f03_evidence/` as reproducible working
evidence. `EG-CP-F03` remains OPEN.

---

## 1. What was proved

```lean
theorem T1_L1_size_only
    (bits1 bits2 : List Bool) (target : Bool)
    (store : RMQ.WordRAM.ReadStore)
    (layout : RMQ.GenericSelect.SparseExceptionSelectTraceSegmentLayout)
    (chunkSeg selSeg c idx : Nat)
    (hlen : bits1.length = bits2.length)
    (hcount : RMQ.GenericSelect.occurrenceCount bits1 target =
              RMQ.GenericSelect.occurrenceCount bits2 target) :
    (RMQ.GenericSelect.sparseExceptionSelectData bits1 target)
        .bpChunkedSelectTraceResultWithStore layout chunkSeg selSeg store c idx =
      (RMQ.GenericSelect.sparseExceptionSelectData bits2 target)
        .bpChunkedSelectTraceResultWithStore layout chunkSeg selSeg store c idx
```

and the route corollary against the actual route function
(`RMQ/Core/SuccinctFinalStoreParam.lean:645-653`):

```lean
theorem L1_route_shape_size_only
    {a b : RMQ.Cartesian.CartesianShape} (h : a.size = b.size)
    (store : RMQ.WordRAM.ReadStore) (idx : Nat) :
    RMQ.SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore a store idx =
      RMQ.SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore b store idx
```

Axioms, verbatim:

```
'T1Map2.T1_L1_size_only'          depends on axioms: [propext, Classical.choice, Quot.sound]
'T1Map2.L1_route_shape_size_only' depends on axioms: [propext, Classical.choice, Quot.sound]
'T1Map2.longFlagLen_congr'        depends on axioms: [propext]
'T1Map2.sparseFlagLen_congr'      depends on axioms: [propext]
```

No `sorryAx`. No `native_decide`/`ofReduceBool`. Files:
`f03_evidence/t1map_layer2.lean` (T1 + corollary), `t1map_obligations.lean`
(O1-O5), `t1map_route.lean` (route bridge), `t1_readprogram_core.lean`
(coordinator's read-program core), `t1_c06_verify2.lean` (verification below).

Reproduce from a worktree with a complete `.lake` build at this commit:

    lake env lean docs/internal/f03_evidence/t1_c06_verify2.lean

---

## 2. Why it goes through — the structural finding

The mapping lane established, by exhaustive scan of the whole body of
`bpChunkedSelectTraceResultWithStore`
(`RMQ/Core/SuccinctClose/RelativeRmmMacro/ChargedRankSelectLeafTrace.lean:1157-1219`):

> **`bits` occurs exactly ONCE in the entire body, in all arms** — line 1168,
> the guard `if idx < occurrenceCount bits target`.

Everything else is a projection of `data`, of which there are ten. Four are
scalar geometry (`wordSize`, `superStride`, `localStride`, `localSlotsPerSuper`),
each `f bits.length` at `Source.lean:2375-2383`. One, `queryOccurrence`, is
**inert** — `Source.lean:1851` binds `_data` and returns `idx`. The remaining
five are tables, and all of them turn out to be content-blind.

The reusable core, found by the coordinator and strengthened by the lane:

```lean
-- RMQ/Core/SuccinctSpace/WordStoreRAM.lean:26-29
def readProgram {payload : List Bool} (_store : PayloadWordStore payload)
    (i : Nat) : WordRAM.Program .optWord := WordRAM.Program.readWord 0 i
```

The store is bound as `_store` — **unused** — so the emitted program is literally
`readWord 0 i`. Every fixed-width table read funnels through it. Consequently
`entryRead_table_irrelevant` holds **by `rfl` with no axioms at all**, and is
stronger than scouted: not even `entries.length` or `fieldWidth` need agree.
This is the same mechanism that closed the interior cone
(`machineReadComputationAt`'s unused `_table`), one level deeper.

**Note what the proof did NOT need.** It never argues that the long/sparse branch
reads a probe reply rather than `superIsLong`. That structural claim is true and
was the coordinator's route in, but the proof is simply a congruence: once the
scalar geometry and the two flag-list lengths agree, the two evaluations coincide
step for step **whatever the branches do**. `superIsLong` never appears in the
trace function at all — only in table construction. This is why T1 is
threshold-free and says nothing about n ≈ 13,276 in its statement.

The two flag-length obligations, which the campaign flagged as the genuinely open
part, were discharged from **existing repo lemmas**: `longSuperFlagBits_length`
and `sparseExceptionEffectiveFlagBits_length`, both expressed through
`superSlotCount`/`localSlotCount`, which are functions of length and occurrence
count. That is exactly what `hcount` supplies, and on the route `hcount` is
discharged automatically because a balanced-parenthesis code has `size`
occurrences of each bit.

---

## 3. Independent verification performed by the coordinator

The workflow lost five agents to upstream `529` errors, including three
verification lanes. The coordinator therefore verified the result directly
(`f03_evidence/t1_c06_verify2.lean`, zero errors):

- **Hypotheses are satisfiable off the diagonal.** `bvA = [T,F,T,F]`,
  `bvB = [F,T,F,T]`: `bvA ≠ bvB` by `decide`, equal length, equal occurrence
  count. So `hlen`/`hcount` do not secretly force `bits1 = bits2`.
- **The route corollary is non-vacuous.** `shapeL = node (node empty empty) empty`
  and `shapeR = node empty (node empty empty)` have equal `size` and
  **provably different `bpCode`** (`by decide`); the corollary was instantiated at
  them.
- **Expected-type pin.** `C06ExpectedT1RouteType` is written independently of the
  theorem's declaration and inhabited by the theorem *value* alone, with no
  reconstruction from neighbouring lemmas.
- **Anti-bypass.** A consumer taking only `a.size = b.size` — not `a = b` —
  typechecks, so the theorem really is the equal-size statement.
- Axioms re-printed on the final theorems, not on components.

---

## 4. What this does and does not close

**Closes.** T1 as specified: the select-close leaf, the row's weakest and the
only obligation reaching past the `superIsLong` crossover. Controller leaf L1 is
size-only, universally in `bits1`, `bits2`, `target`, `store`, `layout`, the
segment parameters and `idx` — no size threshold, no regime restriction.

**Does not close.**

1. **`EG-CP-F03` itself.** The capstone is T4 (whole-query footprint and value),
   which still needs L2 and L3 assembled with this. T3 and T5 remain as recorded.
2. **Controller leaf L2** still has no classification row at all — the process
   gap recorded in the campaign report, including its top-level route selector at
   `ChargedFringeWiring.lean:494-503` and the entire same-block arm.
3. **Nothing is in `RMQ/`.** A grep of `RMQ/` for these names returns zero hits.
   Until Tier 0 porting lands on a green branch, the row has proof but not a
   citable declaration, and no claim may cite it as established.
4. The other campaign gaps are untouched: the inventory was never rebuilt
   (6 of 55), "universal consumers" was never defined, probe counting has no row.

**Newly settled as a side effect.** The campaign's open question about
`longSuperRelativeEntries` / `sparseDirectory.relativeEntries` — whether their
lengths are content-dependent — is **not on T1's path**: the trace function
projects only `flagBits.length` and the rank geometry, never those entry lists.
The question still matters for `EG-CP-F01`'s K = 1 vs K = 3 header decision, but
it is no longer a blocker for geometry closure of this leaf.
