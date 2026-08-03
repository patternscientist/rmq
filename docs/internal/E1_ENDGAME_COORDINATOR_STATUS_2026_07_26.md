# Endgame coordinator status — 2026-07-26

Author: C06 (Claude runtime). For owner review and independent coordinator review.
`origin/main` = `1490c97`. Pending branch `claude/f03-a10-audit-repairs` = `1fd8e57`,
both CI workflows green, **not merged**.

This document assumes no conversation context. It states where the endgame is,
what is decided, what is open, and what I recommend next. Section 8 lists the
places where I am least confident or have an interest, for a reviewer to target.

**No claim here is an acceptance.** Stage F row acceptance is a coordinator act
against the frozen matrix, and no row below is recorded closed.

---

## 1. The target

Ratified 2026-07-26 (`docs/internal/RMQ_ENDGAME_ROADMAP.md`): a **packed counted
cell-probe** RMQ. One read-only array of exact-width `w(n)`-bit cells holding
`header ++ buildPayload ++ padding`, allocated capacity at most `2n + rho(n)` for
checked `rho = o(n)`, queried by a closed controller whose only dynamic inputs are
`n`, the endpoints, and prior probe replies, within a constant probe cap.

Status: **FEASIBILITY CANDIDATE**, not accepted. Fallback is the U3+M1 charged-read
surface, which may not be called a certified floor until U3's fresh-blind audit
closes. Model must be described as cell-probe; **never** as word-RAM time.

Runway: roughly four weeks remain of the window that opened 2026-07-07.

## 2. What is proved and in the library

On `main`, `lake build RMQ` green, axioms `[propext, Classical.choice, Quot.sound]`
throughout, no `sorryAx`, no `native_decide`:

* `RMQ/Core/SuccinctFinal/RAM/GeometryClosure.lean` —
  `T4_wholeQuery_trace_size_only`: for two Cartesian shapes of equal `size`, one
  shared supplied store and any endpoints, the whole-query controller emits an
  identical trace and returns an identical value. Plus the public-entry corollary
  over `List Int` of equal length, a positive factorisation through a witness
  function that mentions no input list, and
  `queryTraceResultWithStore_length_and_footprint`, which weakens the shared-store
  hypothesis to agreement on the **ordered read footprint alone**.
* `RMQ/Core/SuccinctFinal/RAM/SourceInventory.lean` —
  `storeParametricRead_hasListedSource`: every logical read the supplied-store
  controller emits resolves to one of 22 typed sources, universal over every
  shape, store and endpoint pair, no validity side condition.

**Scope fence, load-bearing.** These are theorems about the **supplied-store**
surface. The store-free surface is genuinely content-dependent (two length-10
lists give 96 events against 79) — lawful, since probe replies are an allowed
input, but nothing derived from these may be phrased over "the public query"
without "at a shared supplied store".

## 3. Stage F row status

| Row | Status |
|---|---|
| **F01** header schema | **SUBSTANTIALLY_ADVANCED, not closed.** Schema and `K` frozen; `memory xs` undefined; nothing in `RMQ/`. |
| **F02** header consumption | Scoped. **Unsatisfiable as written** at `K = 1`; blocked structurally by F04. |
| **F03** geometry closure | **OPEN.** Evidence clause amended and merged; **A11 commissioned but NOT RUN**. |
| **F04–F13** | Untouched, except F06's inherited obligation and an early F07 escalation (§6). |

### F01 — frozen

`w n = SuccinctRank.machineWordBits (2n) = Nat.log2 (2n) + 1`, pinned to the
route's own rank divisors. The contract's three all-size inequalities hold with no
side condition; `K_w = 2` is minimal **by checked refutation** (`K_w = 1` fails at
`n = 2`). At `n = 0` the cell is one bit wide — chunking must not assume a byte.

**`K = 1`** (DD-20260726-007): the single field `n`, with both content-dependent
select regions padded to refined `n`-only budgets that are zero below their
thresholds. The decisive argument is that against the **proved** bound padding is
free — the padded allocation already sits inside an overhead the `2n + rho`
capstone charges in full, so `rho` is unchanged and `K = 3` could only recover the
unproved gap between actual and budget, while costing probes (those fields are not
`w(n)`-bounded) and turning the header into a second content channel that would
force the F03 congruence to be reproved.

Both halves must appear in any write-up: the padding is genuinely `o(n)` **and**
genuinely about `n/3` at every reachable size.

Not closed because `memory xs` — the fixed-width chunking the contract defines —
**has no definition anywhere**, so the capstone requirement "`memory xs` has cell
width `w(n)`" has no subject; nothing is in `RMQ/`; and `w` is frozen against the
rank divisors only while the select sub-directories compute their own widths, with
the relating bound still a sketch. About 4–6 focused proof-days.

### F03 — amended, open

An external fresh-blind audit (A10) found the row not closed in letter or spirit
and refuted my central argument. I adopted all four findings, including that my
"strictly stronger" claim was **unsound**: a content-dependent value can be dead or
cancel before any emitted event, so equal traces do not entail that every
intermediate factors through allowed inputs. Retracted in DD-20260726-004.

The owner then directed the amend-then-audit route. The evidence clause was amended
by **adding** two rows with the original text preserved verbatim; the
syntactic-elimination half was relocated to `EG-CP-F06`, whose evidence clause
already reads "cross-shape transcript determinism for equal allowed inputs/probe
replies". A11 is commissioned to audit the amendment, with the verdict split into
"is the amendment legitimate" and "is the amended row satisfied" so rejection is
expressible.

An owner-directed attempt to make the amendment unnecessary produced the source
inventory (landed) and **three rejected deliverables** whose exhaustiveness claims
were false. That failure was structural, and the finding is reusable:

> Exhaustiveness is checkable when the universe is a **closed inductive** — 22
> `ReviewerSource` constructors, joined by case analysis, with the elaborator
> rejecting an unextended table. It is **not** checkable when the universe is
> "every Nat-valued expression in a 917-constant closure", where any census is a
> curated list whose completeness is a separate argument. Three independent
> attempts have now shipped a false exhaustiveness claim on that second half.

## 4. Open decisions

**D1 — merge `1fd8e57`?** Four commits, CI green. Contains the F03 amendment
(which changes a frozen gate row), the A10 disposition, the source inventory, and
the F01 result. Cheaply reversible: the amendment adds rows and preserves the
original text.

**D2 — launch A11.** Written and pinned to target `2a65f8b`, base `6be9e55`. Must
**not** be the A10 auditor; a third model family is preferable. F03 stays open
until it returns. I cannot launch an independent audit of my own work and have it
mean anything.

**D3 — the `FEASIBILITY_PASS` clause at roadmap `:399`** requires "F11 exposes no
small-size model split". That is now **provably violated**: the relative summary
table is dead below `n = 512` over every shape, and interior readiness is **not
monotone** — true from 1000, false again across all of `[1024, 1330]`, true from
1331, because `base` jumps 10→11 at 1024 while `blockCount = n/base` drops 102→93.
`base` jumps again at 2048 and 4096, so further windows are likely and were not
checked. Suggested amendment, now backed by theorems: *every split is a decidable
function of `n` alone, and here are the exact sizes.*

**D4 — F02's disposition.** At `K = 1` the controller never needs to read the
header, because `n` is already a free input under the ratified model. Options are
`K = 0`; a counted dead cell; or making `n` live (probe cell 0, decode, drive
geometry from the decoded value). The campaign adjudicates for the third as the
only one under which F02 stays a real evidence gate rather than a row closed by
amendment. **Caveat that must survive into any amendment: to probe an aligned
`w(n)`-bit cell you must already know `w(n)`, hence `n`. A header read can never be
the source of `n` for its own addressing. No write-up may call the array
self-describing.**

**D5 — strengthen F02's minimum evidence** before any worker starts. "Executed read
trace plus value equality" is exactly the predicate a host mirror makes true, and
this tree already contains a working mirror: `FlatPayload.lean` proves offsets at
`:789-838` and then ignores them at `:861-868`, matching on `segment`. Suggested
addition: *a store differing only at the header cell must change the ordered read
footprint or the returned value.*

## 5. Suggested next moves

Ordered by what unblocks the most, given four weeks.

**M1 — define `memory xs`, and F04 with it.** This is the keystone and it is
currently the bottleneck for three rows. F04 blocks F02 **structurally**: the
controller addresses `(segment, index)` with literal segment numerals and every
region re-based at its own index 0, so there is *no base-offset arithmetic anywhere
in the executed route* — no site exists that could consume a header field, at any
`K`. Until `memory xs` exists, F01 cannot close, F02 cannot start, and F05's
allocated-capacity theorem has no subject. Everything else in Stage F is downstream
of this one definition.

**M2 — the uniform cell width.** One physical width for the whole memory. `w` is
pinned to the rank divisors; the select sub-directories compute their own. The
sketch is monotonicity plus existing flag-length bounds. Small, and F01 cannot close
without it.

**M3 — port F01 into `RMQ/`.** The definitions typecheck but live outside the build
and outside the prose-hygiene scan. Cheap, and it converts the schema from a
document into something citable by commit.

**M4 — the sparse composition lemma.** 1–2 days, closes the one named gap in the
`K = 1` decision. No outcome favours `K = 3`.

**M5 — F07 early.** See §6; I would not leave this to F07's slot.

I would **not** commission another standalone geometry inventory. F06 should
discover its enumeration by performing the packed rewrite, which visits every site
by construction and cannot have the completeness failure mode (recorded as
WDD-20260726-010).

## 6. Risks and early warnings

**F07, escalated ahead of its slot.** Attempted probes return nothing into segment
0 under the **canonical** store at `n = 1,2,3,4,8..12,20,21,24,28,32,36`. F07
requires every valid-query attempted probe to be in range and successful. This is
an existence observation — not characterised, not proved unavoidable, possibly an
artifact of how the canonical store chunks the BP code. It is exactly the class of
finding that ruins a gate late.

**F08 probe cap.** Canonical weighted cost runs 45 at `n = 1` to 118 at `n = 32`
against the frozen bound of 210, over a small sample. The bound is a proved
theorem, so growth is bounded — but a **physical** cap must be derived from the
packed trace, and a cell crossing can cost two probes. Expect a constant above 210.
The roadmap already allows "`210` plus descriptor/packing overhead, or another
constant"; reusing `210` by prose is forbidden.

**Kernel opacity.** The route does not reduce in the kernel — `decide` cannot close
even reflexivity of the trace, because the select data bundles tactic-generated
proof fields. Consequence: anti-vacuity witnesses of the form "the transcript
varies with `n`/endpoints/replies" **cannot be obtained by kernel evaluation at any
size** and must be proved. Any row whose evidence clause names an executed witness
should be read with this in mind.

**Evaluation ceiling.** Interpreted evaluation of the LCA leaf is superlinear
(~180 s per evaluation at `n = 128`), and interior macro arms first become
realizable around `n ≈ 3457`. Large-`n` executable evidence is not available;
proof is the only instrument above the walls.

## 7. Corrections carried forward

Two figures I circulated earlier are wrong and any document keyed to them needs
re-keying:

* The `superIsLong` crossover is **5488/5489**, not ~8192. The earlier figure came
  from a power-of-two-only scan.
* `canonicalBPRelativeMinMaxArgSummaryTableActive` **is** executable-path relevant.
  I had reported it was not in the controller's computational core; it gates store
  content and a live branch.

## 8. Where to target a review

Places where I am least confident, or have an interest:

1. **The F03 amendment is authored by the party whose work the audit found short**,
   and it makes that work sufficient. Its load-bearing claim is that the inventory
   was doing F06's job inside F03. A reviewer should read F06's row and decide
   whether that reading is honest or convenient. A11 is asked exactly this.
2. **The closed-inductive-versus-geometry exhaustiveness claim** (§3) is doing a lot
   of work for the amendment, and it arrived from an attempt to defeat the
   amendment, which is the kind of coincidence worth checking rather than trusting.
3. **The `K = 1` space argument** rests on the padded allocation already sitting
   inside a charged overhead. If that composition is wrong, the decision changes.
   One half was closed during verification; the sparse half is open.
4. **F01's arity gate 1** rests on Lean's match-exhaustiveness checker and has no
   proposition to negate. Two of the three gates have checked controls; that one is
   argued, not checked.
5. **`SourceInventory` proves segment-to-LABEL, not segment-to-WORDS**, so the
   `{0,19}` alias is an equality of labels rather than returned words. The module
   says so; a reviewer should confirm nothing downstream assumes otherwise.
6. My own hygiene record this session was poor — four mechanical defects (a prose
   regex hit inside a docstring, two EOF blank lines, and validating a different
   commit range than CI does), each caught by a gate rather than by me. A pre-push
   script that runs exactly what CI runs, per commit, is not yet written.
