# EG-CP final falsification gate — worker result

**Status: INCOMPLETE — in progress.** This document is the durable worker report
required by the checkout contract. It is written and updated as the branch
proceeds so that a successor session can resume from commits alone; it is not a
completion claim. No row of the frozen matrix is closed, and neither
`CANDIDATE_COMPLETE` nor an obstruction is being asserted.

Worker: Claude (Opus 5) runtime, role skill `rmq-proof-sprint`.
Branch: `codex/eg-cp-final-falsification-gate-r1`.
Base: `1490c97b399d136bad4e18953441da433d130d4d`, tree
`4114fe2544ad0a4af4dce3c002e617a8dd55e64b`, both verified.
Governance ref `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5` verified as an ancestor.
Worktree: `C:\Users\poin\.codex\visualizations\2026\07\17\019f6d85-7626-7433-a60b-81f8be29689a\eg-cp-final-falsification-r1`.
Never pushed, never merged.

---

## 1. Preflight

`scripts/project_skill_preflight.ps1` against the governance ref, with
`rmq-proof-sprint` required: **PASS**.

The runtime catalog was declared as `rmq-proof-sprint` alone. That is the only
project skill for which runtime evidence exists — it was invoked successfully
through the Skill tool. `rmq-audit-prompt` and `rmq-coordinator` are present under
`.claude/skills` and `.agents/skills`, but filesystem presence is not runtime
evidence and the contract says so explicitly. Declaring the smaller set can only
make the check stricter, never produce a false pass.

## 2. Commit ancestry

```
5ab003d  Prove the packed memory round trip
ca11556  Define the packed memory: cells, allocation, and the header cell
52e7988  Fix the K=1 header schema: P n, w n, all-size count fit, decoding
85c58f0  Close the shape-free address-factorization leaf for FG-02 and FG-03
b9ace55  Add a decidable size-only counting guard for the close sources
17d1ddf  Make the rank prefix a Nat-only mirror and prove sparse terminality
63fd605  Mirror the select super geometry and isolate the long-count term
319aabf  Prove the packed close-component base is input-size-only
0a18548  Freeze the EG-CP final falsification acceptance matrix
1490c97  (base)
```

The freeze at `0a18548` precedes every implementation edit, so the freeze is
git-verifiable rather than asserted. Every commit was validated individually with
`scripts/design_decision_check.ps1 -Strict -Base HEAD~1`, which is how CI evaluates
them (`WDD-20260726-007`), and with `git diff --check HEAD~1..HEAD`.

## 3. What is proved

All declarations live under `RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/` and are
imported by `RMQ.lean`, so they are inside `lake build RMQ` and inside the prose
hygiene scan.

### The K1 address factorization (`FG-02`, `FG-03` — leaf complete, rows Open)

```
packedSourceComponentOffset :
  Nat -> Nat -> ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Nat

packedSourceComponentOffset_eq :
  forall (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource),
    concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset shape source =
      packedSourceComponentOffset shape.size (longCount shape) source
```

The signature carries the claim: with no shape argument no instantiation can
consult shape content. Coverage is elaborator-enforced — the proof is
`cases source`, so a new constructor fails to elaborate until both sides supply
its arm, and the `finalRankBPCodeAlias` alias, the three retired finite-small
slots and the zero arms each appear explicitly rather than under a default.

Component bases: `closeComponent_flatOffset` gives
`componentFlatOffset .closePayload = 2 * shape.size + packedAccessOverhead shape.size`.
The whole select payload, including *both* content-dependent relative tables, is
absorbed by the access padding. This is not arithmetic luck: truncated `Nat`
subtraction makes `a + (B - a) = B` false without `a <= B`, and that hypothesis is
the `BPCloseAccessDirectory.payload_length_le_overhead` structure field, so the
layout cannot be instantiated without it.

Terminality: `selectPayload_eq_prefix_append_sparseRelative` exhibits the select
payload as a prefix that does not mention the sparse relative table, followed by
that table; `selectSourceComponentOffset_le_prefix` gives the addressing
consequence.

The long-count term:

```
longSuperRelativeTable_length_eq :
  (GenericSelect.longSuperRelativeTable shape.bpCode false).payload.length =
    longCount shape *
      (GenericSelect.superStride (2 * shape.size) *
        GenericSelect.wordBits (2 * shape.size))
```

### The counting guard (`FG-02` support)

`PackedSummaryActive` and `PackedInteriorReady` are decidable predicates on `Nat`,
with `summaryActive_iff_packed`, `interiorReady_iff_packed` and
`sourceCounted_iff_packed` proving agreement with
`concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat` on every constructor.

This is load-bearing rather than bookkeeping — see section 5.

### The `K = 1` header (`FG-04` — clauses proved, row Open)

`packedPayloadLength n = 2 * n + concreteBPNativeSuccinctRMQOverhead
genericSparseExceptionBPCloseAccessOverhead n`, with `packedPayloadLength_eq`;
`packedCellWidth n = SuccinctRank.machineWordBits (packedPayloadLength n + 2)`,
the commissioned expression unchanged; `longCount_lt_two_pow_width` with no size
side condition; `packedHeaderBits_length` (exact one-cell arity);
`packedHeaderBits_decode`. Empty and singleton instantiated as kernel-checked
examples.

### The packed memory (`FG-05` — partial)

`packedSerializedBits`, `packedCellCount`, `packedAllocatedBits`,
`packedPaddedBits`, `packedMemory`, with `packedMemory_length`,
`packedMemory_cell_length` (every allocated cell exactly one full width, none
short), `packedMemory_cell_zero` (header is cell zero in full),
`packedMemory_flatten` (join recovers the padded bits exactly) and
`packedMemory_flatten_take`.

## 4. Exact-type consumers

`RMQ/Validation/EGCPFinalFalsification.lean` states each dependency's expected
type independently and discharges it with the library result, so weakening a
library theorem breaks that file rather than being absorbed by it. It pins the
shape-free signature, the factorization, the close base, terminality, the counting
guard, the long-count term, `P`, `w`, the count fit, header arity and decoding.

`#print axioms` over a theorem's current type would not do this: it reports what a
declaration happens to say now. These consumers say what it must say.

## 5. A defect found in the existing layout

`concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset` computes the two
close-interior offsets **unconditionally** (`FlatPayload.lean:523-526`), while
`concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat` counts those sources
only when the interior is ready. Outside that regime the offsets point past the
end of the close component.

Today this is discharged only by `CountedInFlat` appearing as a *hypothesis* on
`concreteBPNativeSuccinctRMQFlatPayloadSource_component_slice`. A controller has no
such hypothesis available at run time: it must decide readiness. That is why
`interiorReady_iff_packed` matters — readiness is decidable from `n`, so the guard
costs no header field, but it has to be in the controller rather than in a proof.

This is plausibly the same phenomenon as the `EG-CP-F01` campaign's escalation to
`F07` (attempted probes returning `none` into segment 0 under canonical stores at
small `n`). That has not been checked and should not be assumed.

## 6. Corrections made to this branch's own records

Recorded in `DESIGN_DECISIONS.md` under
"Correction to the `DD-20260802-001` evidence note".

1. An earlier evidence note called the long relative table "the only length
   reachable from a select offset that the input size does not fix". That was a
   projection from a partial map. The proved conclusion is narrower and
   conditional: `longCount` is the only content-dependent **prefix** length needed
   to locate later live select sources, **conditional on** terminality.
2. The same note read `offsets_congr` (`GeometryClosure.lean:718`) as showing the
   close side "needs no descriptor at all". That is a size **congruence**, over
   the reviewer interior component at machine-word granularity, not an executable
   size-only mirror over the flat payload. A congruence says offsets are
   determined by the size; a controller cannot evaluate a determination. No claim
   about the `K = 0` flip is made.

## 7. What is not done

`FG-01` (payload identity) is not separately stated. `FG-05` lacks the
cell-crossing slice behaviour and the all-reads-target-this-object theorem.
`FG-06` through `FG-15` are not started: allocated-space bound and its little-o
proof, the closed controller, physical lowering, totality and the derived probe
cap, same-run correctness, liveness and anti-bypass, boundaries, trust, the
sixteen-case committed replay harness, and the durable decision set.

`FG-07` and `FG-10` are the bulk of the remaining work: a shape-free controller
whose actual execution reproduces the project's reference semantics. Nothing so
far constructs one, so every row that quantifies over "the packed execution"
— including `FG-02` and `FG-03`, whose leaves are complete — remains Open on that
dependency.

## 8. What a skeptical reviewer should ask

- The factorization is about **bit offsets**. Spans, cell crossings and
  reachability are not covered. Does the row's phrase "offset and span" require
  more than is proved? (Yes, and the matrix says so.)
- `packedSourceComponentOffset` is proved equal to the canonical offset, but
  nothing yet *calls* it. Until the controller does, is this a factorization of
  the executed addressing or only of a definition that happens to describe it?
- The mirrors are `Nat`-only by signature. Are any of them nonetheless computing
  something a controller could not, e.g. depending on a quantity only derivable
  from the shape? Each has an equality theorem; check the equalities, not the
  names.
- `PackedSummaryActive` is a six-conjunct decidable predicate. Is it actually
  decidable in the sense a controller needs, or merely `Decidable` in Lean?
- The close side's step function is non-monotone in `n`. Does any later row
  assume monotonicity?

## 9. Verification

`lake build RMQ`: green; cold baseline 683 s, incremental 10–80 s. Hygiene scan
over `RMQ lakefile.toml` and the `native_decide` / `Lean.ofReduceBool` scan: both
clean. `claim_drift_scan.ps1 -Strict`: exit 0, 0 strict failures.
`design_decision_check.ps1 -Strict -Base HEAD~1`: clean on every commit.
`git diff --check`: clean on every commit.

The aggregate `scripts/gate.ps1`, the replay harness and the focused final checks
have **not** been run; they are reserved for a final tree that does not yet exist.
