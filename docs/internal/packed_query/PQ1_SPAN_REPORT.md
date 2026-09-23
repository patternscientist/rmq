Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

This declaration concerns the bounded PQ1-S numeric span/repacked-loader leaf
assigned by `PQ1_SPAN_PROMPT.md`, not the fully charged query capstone.

Worker: PQ1-S (`numeric_span`). Branch: `codex/fully-charged-packed-query-v1`.
Worktree: `C:/Users/poin/.codex/worktrees/a84a/RMQ`.
Base and governance: `4639223bc8130b0ef752270b5cbdd74325abcd60`.
No staging or commits were performed; the lead owns integration.

The required `rmq-proof-sprint` preflight passed with the actual runtime catalog
`rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`. The canonical skill,
completion gate, relevant failure modes, E1 roadmap, and the lead's dense
packing design were read before proof changes. The four explicit requirements
and six assigned inherited invariants were frozen verbatim in
`PQ1_SPAN_MATRIX.md` before implementation. The final exact-text verification
passes under strict UTF-8 and preserves every frozen requirement.

Changed owned files:

- `RMQ/Core/WordRAM/Packed/Span.lean`
- `docs/internal/packed_query/PQ1_SPAN_MATRIX.md`
- `docs/internal/packed_query/PQ1_SPAN_REPORT.md`

No shared interface, root task title, original checkout, audit checkout,
lead-owned file, or existing decision ledger was modified by this worker.

## Exact construction and theorem evidence

All declarations below are in `RMQ.SuccinctFinal.PackedWordRAM` and available by
importing `RMQ.Core.WordRAM.Packed.Span`.

`spanPlan width position len` is `[]` for zero length; otherwise it is
`[position / width]` if `position % width + len ≤ width`, and
`[position / width, position / width + 1]` otherwise.

`decodeSpanNat width position len memory` returns `some 0` before reading if
length is zero. Otherwise it binds the numeric first cell. The contained branch
returns `some (first / 2^(position % width) % 2^len)`. The crossing branch binds
the second numeric cell and returns

```text
some (first / 2^(position % width) +
  (second % 2^(len - (width - position % width))) *
    2^(width - position % width))
```

Neither a semantic answer nor a bit-list callback appears in the executable
arguments. `Option` carries physical absence separately from raw numeric data;
the all-ones full-width word never needs a `+1` tag. Masking the second fragment
before shifting avoids a temporary concatenation of two whole physical words.

The kernel-checked universal span conclusion is:

```lean
theorem decodeSpanNat_uniform (cells : List (List Bool)) (width position len : Nat)
    (hw : 0 < width) (hwidth : ∀ cell ∈ cells, cell.length = width)
    (hlen : len ≤ width) (hbound : position + len ≤ cells.length * width) :
    decodeSpanNat width position len (cells.map bitsToNatLE) =
      some (bitsToNatLE ((cells.flatten.drop position).take len))
```

The assigned downstream join for this leaf is inhabited without readiness,
content, or desired-reply assumptions:

```lean
theorem loadOldCellNat_repacked (headers : List Nat) (width oldWidth : Nat)
    (old : List (List Bool)) (hOld : ∀ cell ∈ old, cell.length = oldWidth)
    (hOldPos : 0 < oldWidth) (hOldLe : oldWidth ≤ width) (index : Nat) :
    loadOldCellNat headers.length width oldWidth old.length
      (repackWords headers width old) index = (old[index]?).map bitsToNatLE
```

The executable loader first checks `index < oldCount`; a passing guard decodes
the span at `headerCount * width + index * oldWidth` with length `oldWidth`.
All values are numeric scalars or `List Nat`. Header bounds are not needed in
the exactness theorem because no header value is examined. Thus the theorem
covers every bounded header list required by the contract, and also arbitrary
header values; the allocation's existing width theorem separately supplies
their storage bounds.

The identity chain is literal:

```text
repackWords headers width old
= headers ++ denseWords width old.flatten
  -- decodeSpanNat_append_shift removes exactly headers.length physical words
→ denseCells width old.flatten mapped through bitsToNatLE
  -- decodeSpanNat_uniform
→ denseCells.flatten bit slice
  -- denseCells_flatten; densePad_slice; uniform_flatten_slice
→ (old[index]?).map bitsToNatLE
```

This is the exact `repackWords` object appearing in the lead-owned
`repackWords_capacity_le`. `repackedLoader_expectedType` independently spells
out `headers ++ denseWords width old.flatten` in its proposition and consumes
the universal loader theorem with all original-cell option arguments fixed.
Every local bit-slice helper introduced for the join is consumed by it.

`spanPlan_length_le` proves plan length at most two for every numeric argument,
without positivity premises. `decodeSpanNat_isSome_iff` proves:

```lean
(decodeSpanNat width position len memory).isSome ↔
  ∀ address ∈ spanPlan width position len, (memory[address]?).isSome
```

`decodeSpanNat_read_backing` strengthens the read use to positional occurrences:
for every `occurrence < (spanPlan width position len).length`, success implies

```lean
∃ word, memory[(spanPlan width position len)[occurrence]]? = some word
```

`decodeSpanNat_none_of_missing` proves that a missing reply at any such
occurrence forces the whole decoder result to `none`. `decodeSpanNat_congr`
proves equality of the full returned `Option Nat` whenever two numeric memories
agree at every positional planned occurrence. These are functional read
theorems. The geometric plan is not represented as an executed failure trace:
the first missing bind short-circuits evaluation before a second read.

## Boundary and anti-vacuity evidence

Ten direct `by decide` examples and the named `crossing_value_dependency`
theorem elaborate in the module. Their expected values are explicit numeric
bit slices, and all consumers use the new decoder or the concrete repacking:

| Case | Checked result |
| --- | --- |
| Width 4, position 1, length 2, memory `[13]` | Plan `[0]`; result `some 2` |
| Width 4, position 3, length 3, memory `[13, 3]` | Plan `[0, 1]`; result `some 7` |
| Three old 3-bit cells, width 4, two headers, final old-cell index 2 | Concrete `repackWords` returns `some 6` across the final padded physical cell |
| Width 4, position 8, length 0, two physical cells | Empty plan; result `some 0` |
| Crossing with required second cell absent | `none` |
| Nonempty span with required first cell absent | `none` |
| Old-cell index equal to oldCount | `none` |
| Full-width raw cell `[15]` at width 4 | `some 15`, with no option-tag overflow |
| Crossing first reply changed from 13 to 5 | Returned value changes from 7 to 6 |
| Crossing second reply changed from 3 to 2 | Returned value changes from 7 to 5 |
| Zero span in entirely absent physical memory | `some 0` |

The value-dependency claim is the exact inequality between these returned
options, rather than inequality of a trace record whose log could differ.
The universal congruence claim has the precise positional-agreement predicate
as its premise; no claim that every changed physical bit must affect every
span is inferred from the examples. For zero-length and absence claims the
same decoder expression appears in the premise and conclusion of each backing
or boundary theorem. No external or report-only mutation campaign is claimed.

## Verification

One Lean process was used at a time, with the build slot exchanged explicitly
with the lead and primitive-calculus worker. Development errors were narrow
proof/simplifier issues; no command timed out and no unchanged expensive run
was repeated. Final source SHA256:

`70b0999b80f2a7a97933e8c4663b552da845b3b1467aba3c731fe23f05df04b2`.

Final command:

```powershell
$env:LEAN_PATH = (Join-Path (Get-Location) '.lake/build/lib/lean')
& C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe `
  -o .lake/build/lib/lean/RMQ/Core/WordRAM/Packed/Span.olean `
  RMQ/Core/WordRAM/Packed/Span.lean
```

Result: exit 0, no warnings, 5.30 seconds; local `Span.olean` is available to
the lead. The build slot was released immediately afterward.

The owned Lean hygiene scan found no occurrences of the trust-shortcut
vocabulary, Mathlib imports, `native_decide`, or `Lean.ofReduceBool`.
Working-tree whitespace and no-index checks for newly created owned files
passed. Strict UTF-8 comparison verifies all four prompt requirement blocks
and six inherited invariant blocks, rejecting missing or duplicate blocks.

As explicitly assigned, the lead owns final strict design-policy validation
against the exact base, committed-range whitespace after integration, broad
builds, whole-query gates, and the eventual public exact-commit audit. None of
those broader results is claimed by this leaf report. No workflow change was
made, so no workflow decision entry is needed.

## Proposed decision-ledger detail for lead integration

Suggested addition under DD-20260910-PQ1-001:

The numeric repacked-cell adapter reads at most two consecutive physical cells
and proves equality to the original cell option for every index. It shifts the
first reply down and masks the second fragment before shifting up, preserving
absence separately with `Option Nat`. The rejected alternative was numeric
concatenation `first + 2^width * second`, which would require a double-width
intermediate. A header-prefix shift theorem uses only header count, so numeric
header contents remain irrelevant to this representation proof while still
being counted and width-bounded by the concrete allocation theorem. The
consequence is a usable scalar specification for primitive compilation, with
no new semantic callback or uncharged execution claim. Evidence:
`decodeSpanNat_uniform`, `loadOldCellNat_repacked`, positional read backing,
`repackedLoader_expectedType`, and the all-ones/crossing/absence consumers in
`RMQ/Core/WordRAM/Packed/Span.lean`.

## Proof digestion

Conceptually, the proof separates two independent representation changes:
skipping a full-word header prefix and slicing a densely repacked bit stream.
Little-endian drop/take identities turn the bit-list slice into the same
division, remainder, multiplication, and addition computed from numeric cells.
Uniform cell lengths then identify the result with one original cell.

In plain English, changing the physical word size no longer loses access to
the old memory: the numeric loader reconstructs any old cell exactly from one
or two new words, including when the final new word contains padding. Missing
cells and invalid old indices stay missing.

Live assumptions are positive old-cell width, old width at most the selected
physical width, and uniform original-cell lengths. The generic span theorem
also requires its span to lie inside full-width physical capacity. There is no
shape, readiness, small-fixture, or semantic-result assumption.

A skeptical reader should inspect the crossing fragment length and shift, the
header-count address translation, the zero-length endpoint case, and the
positional backing theorem. The lead's expressly separate primitive consumer
will establish instruction-level execution and arithmetic/address widths for
this numeric computation; this report makes no claim about those machine
properties or native Lean runtime.
