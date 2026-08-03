# EG-CP-F01 header schema — result

Coordinator: C06 (Claude runtime). Date: 2026-07-26.
Governed base: `1490c97` (`origin/main`).
Rows: `EG-CP-F01-HEADER-SCHEMA` (`RMQ_ENDGAME_ROADMAP.md:372`), scoping
`EG-CP-F02-HEADER-CONSUMPTION` (`:373`).

**This record accepts no theorem and makes no public claim.** All definitions
below live in `docs/internal/f01_evidence/`; **nothing is in `RMQ/`.**

---

## 1. Verdict

| | |
|---|---|
| **All-size arity/width theorems** | **MET.** Every statement is quantified over all `n` with no side condition; `n = 0` and `n = 1` instantiated and independently checked. |
| **Checked definitions** | **NOT MET.** `memory xs` does not exist; nothing is in the library; the width is frozen against one directory only. |
| **Row status** | **`SUBSTANTIALLY_ADVANCED`, not `CLOSED`.** Roughly 4–6 proof-days of named distance. |
| **`K`** | **`K = 1`, DECIDED on evidence.** One named composition gap on the sparse half, 1–2 days. |

Recorded as not-closed deliberately. The schema and `K` are frozen and downstream
lanes may build against them, but a blind auditor handed a schema whose
`memory xs` has no definition will say the same thing, and the last two rows were
both judged not-closed externally.

## 2. The frozen schema

**Width.** `w n = SuccinctRank.machineWordBits (2 * n)`, closed form
`Nat.log2 (2 * n) + 1` by `rfl`. Frozen because it is the route's:
`builtRelativeSplitBPCloseRankWordSize shape = machineWordBits shape.bpCode.length`
(`RMQ/Core/SuccinctFinal.lean:767-769`) with `bpCode.length = 2 * size`
(`Shape.lean:51-52`); `blocksPerSuper` is `rfl`-equal to it, so one `w` serves
both rank divisors (`SuccinctRank.lean:142-143`).

All-size inequalities in the contract's exact shape (`:308-311`), each with no
side condition: `1 <= w n`; `n < 2 ^ w n`; `w n <= K_w * (Nat.log2 (n+1) + 1)`
with **`K_w = 2`, minimal by checked refutation** — `K_w = 1` is refuted at
`n = 2`, where `w 2 = 3` against `Nat.log2 3 + 1 = 2`.

Pins: `w 0 = 1`, `w 1 = 2`; `w` on `0..8` is `[1,2,3,3,4,4,4,4,5]`;
`(w 512, w 1024, w 8192) = (11,12,15)`. **At `n = 0` the cell is one bit wide** —
chunking must not assume a byte.

**Header, `K = 1`.** A closed one-constructor universe `HeaderField.size`;
`frozenValue xs .size = xs.length`; encoder is the repo's own
`natToBitsLE`/`bitsToNatLE` (`SuccinctSpace/WordStore.lean:26-34`), shared with
the payload words. `payloadBits` is **definitionally** `buildPayload`, per the
contract's `:314-317` clause. Domain is `List Int`, forced by that clause.

`headerBits.length = w n` exactly, so the header is cell 0 in full, zero padding,
one probe, at every `n`. The payload starts at cell 1 uniformly and no header
field straddles a cell, so the `:340-343` two-probe rule never fires on it.

Arity is elaborator-gated in three places, two with checked controls proving the
negation of what they would otherwise have to discharge. **The third gate rests
on Lean's match-exhaustiveness checker and has no proposition to negate — that is
argued, not checked**, and is stated as such.

## 3. The `K` decision

**`K = 1`, with both content-dependent select regions padded to refined `n`-only
budgets.** The refined budgets are zero below their thresholds rather than always
charging the worst case:

* `refinedLongBudget n` is **zero on exactly `[0, 5487]`**, then about `25%` of
  `2n`, settling near `17%`. Exactly one flip below 300000; monotone.
* `refinedSparseBudget n` is **zero for every `n < 2^96`** — zero at every size
  anyone will ever build.

Both are proved unconditional upper bounds on the actual region payloads over
every shape, and both allocations are explicitly counted; nothing is free.

**Against the proved bound, padding is free.** The padded allocation sits inside
`genericSparseExceptionBPCloseAccessOverhead n`, which the existing `2n + rho n`
capstone already charges in full (`SuccinctFinal.lean:1237-1240`). So `rho` is
**unchanged**, not merely still little-o, and `K = 3` cannot improve the proved
bound at all — it could only recover the unproved gap between actual and budget.

Both halves of this sentence must appear in any write-up: the padding is
genuinely `o(n)`, **and** it is genuinely about `n/3` at every reachable size.

Why not `K = 3`: a `K = 3` field is not `w(n)`-bounded (at `n = 1024` the sparse
base ranges to `262656` against a 12-bit cell), so under `:340-343` each costs at
least two probes and inflates the derived cap `C` — `K = 3` is not "three cells
instead of one". It also makes the header a second content channel, so the merged
F03 congruence would have to be restated and reproved rather than surviving the
`:386` re-check verbatim; and it triples the forgeable surface for F10/F13.

**Open gap, named:** space neutrality needs `R + A + B <= T` where the proof
gives `A + B <= T`. The long half was closed during verification
(`padded_long_composes`). The sparse half is **not** the same one-line edit — the
sparse budget enters one level down inside `canonicalSparseExceptionDirectoryOverhead`
and needs the analogous region-wise decomposition. 1–2 proof-days. Confined to the
`n >= 2^96` branch in practice, but required for an all-size theorem. **No outcome
of that lemma favours `K = 3`.**

## 4. Two corrections to the coordinator's brief

1. **The `superIsLong` crossover is 5488/5489, not ~8192.** The earlier figure
   came from a power-of-two-only scan. `2n < longSpanOfSize n` holds on exactly
   `[0, 5487]` and fails from `5488`. **Every prior "empty in every reachable
   regime" claim keyed to 8192 must be re-keyed.**
2. **`canonicalBPRelativeMinMaxArgSummaryTableActive` IS executable-path
   relevant.** The coordinator told the campaign it "was found NOT to be in the
   controller's computational core". It gates store content and a live three-way
   branch at `InteriorDirectory.lean:900-911`.

## 5. Owner decisions this raises

**(a) `FEASIBILITY_PASS` clause `:399` is provably violated as written.** It
requires "F11 exposes no small-size model split". Three splits are now proved:
the relative summary table is dead below `n = 512` (all four store word arrays
are `#[]`, over every shape); a third interior arm exists on `512..999`; and
**`concreteBPRelativeRmmInteriorReady` is not monotone** — true from 1000, false
again across all of `[1024, 1330]`, permanently true from 1331, because `base`
jumps 10→11 at 1024 while `blockCount = n/base` drops 102→93. `base` jumps again
at 2048, 4096, …, so **more such windows are likely and were not checked**.

The defensible amendment, now backed by theorems: *every split is a decidable
function of `n` alone, and here are the exact sizes.* Compatible with the model
contract, since the controller computes all of them from the single header field.

**(b) F02 is unsatisfiable as written at `K = 1`.** The contract makes `n` a free
dynamic input and every geometry value is a closed function of `n`, so the
controller never needs to read the header. Three dispositions; the campaign
adjudicates for **D3 — make `n` live**: the controller probes cell 0, decodes `n`,
and drives geometry from the decoded value. It costs one cell and 2–3 proof-days
and is the only disposition under which F02 stays a real evidence gate rather than
a row closed by amendment, which matters because `:395` requires F01–F08 closed
"by kernel/model theorems, not prose".

**Bootstrap caveat that must appear in any amendment**: to probe an aligned
`w(n)`-bit cell you must already know `w(n)`, hence `n`. A header read can never
be the source of `n` for its own addressing. D3 is redundant-but-sound, not
circular. **No write-up may call the packed array self-describing.**

**(c) F02's minimum evidence should be strengthened before any worker starts.**
"Executed read trace plus value equality" is exactly the predicate a host mirror
makes true, and the tree already contains a working mirror — `FlatPayload.lean`
proves offsets at `:789-838` and then ignores them at `:861-868`, matching on
`segment` instead. Add: *a store differing only at the header cell must change the
ordered read footprint or the returned value.* One line; materially changes what
the row proves.

## 6. Escalation to F07, ahead of its slot

Attempted probes return `none` into segment 0 under the **canonical** store at
`n = 1,2,3,4,8..12,20,21,24,28,32,36`. `EG-CP-F07` requires every valid-query
attempted probe to be in range and successful. This is an **existence
observation** — not characterised, not proved unavoidable, possibly an artifact of
how the canonical store chunks the BP code. It is exactly the class of finding
that ruins a gate on day 6, so it is recorded now.

## 7. Residual

* **R1** Nothing is in `RMQ/`. Definitions are outside `lake build`, outside the
  prose-hygiene scan, and unreferenced.
* **R2** Define `memory xs` — the fixed-width chunking of `serializedBits xs` with
  counted padding. Until it exists, "header occupies cell 0" is length arithmetic
  about an object with no cells, and capstone requirement `:351` has no subject.
* **R3** One physical cell width for the whole memory. `w` is pinned to the
  BP-close rank divisors; the select sub-directories compute their own logical
  widths (`GenericSelect/FlagRank.lean:21-22`, `:208-211`). That these are `<= w n`
  is a **sketch** via monotonicity, not a result.
* **R4** The sparse composition lemma of section 3.
* **R5** F04 blocks F02 structurally: the controller addresses `(segment, index)`
  with literal segment numerals and every region re-based at its own index 0
  (`Segments.lean:24-79`, `:101-165`), so **no base-offset arithmetic exists
  anywhere in the executed route** — there is no site that could consume a header
  field, at any `K`.
