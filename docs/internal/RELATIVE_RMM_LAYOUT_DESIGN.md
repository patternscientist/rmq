# Relative RmM Layout Design

Status: implemented at `03043fe` and accepted by external audit A03 at
`16e378c`.
Pinned source frontier: `25395d43deea39cdbac2c273c60d1298c93cc2f3`.

This document joins the F0 declaration-closure, P1 parameter-design, and N1
architecture scouts. It freezes the U1 interface target only. It does not
choose the U2 small-directory implementation.

## Implementation Outcome

U1 landed the four-field computational `RelativeRmm.Layout` and the separate
`Layout.Valid`, `Layout.SummaryFits`, and `Layout.CompactReady` predicates.
Checked equivalences identify canonical `SummaryFits` with legacy `Active` and
canonical `CompactReady` with legacy `Ready`; fieldwise agreement lemmas keep
the existing Ready route unchanged.

The raw upper-cover theorem now lives beside the raw formulas in
`RelativeSummary.lean`. No final-query dispatch, payload representation, trace,
cost constant, headline alias, or artifact claim changed. This is an interface
and proof-dependency milestone; U2 remains responsible for consuming the layout
in one all-size directory route.

Prospective `U1 should` and `U1 must` language below is retained as the frozen
acceptance specification; A03 checked those obligations against the landed
source.

## Problem

The raw relative-rmM formulas are already total:

- block size and blocks-per-superblock are positive;
- relative width is positive;
- block count is truthful and is zero only when there are no full blocks;
- sentinel-inclusive sample-slot counts are derived from truthful counts.

The defect is in the current public canonical projections. The predicate
`canonicalBPRelativeMinMaxArgSummaryTableActive` combines intrinsic codec
facts, payload budgets, and one-word fit. When it is false, the wrappers replace
valid block size, block count, sample count, and relative width with zero. The
query then interprets zero block size as a reason to enter the structural
zero-block replay.

U1 must make storage readiness incapable of changing geometry.

## Frozen U1 Decision

### Computational data stays separate from proofs

Use one small computational record:

```lean
namespace RMQ.SuccinctClose.RelativeRmm

structure Layout where
  blockSize : Nat
  blocksPerSuper : Nat
  blockCount : Nat
  relativeWidth : Nat

def canonicalLayout
    (shape : Cartesian.CartesianShape) : Layout where
  blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  blocksPerSuper := canonicalBPRelativeSummaryBlocksPerSuperRaw shape
  blockCount := canonicalBPRelativeSummaryBlockCountRaw shape
  relativeWidth := canonicalBPRelativeSummaryRelativeWidthRaw shape
```

The record is not shape-indexed and does not carry proof fields. This keeps
runtime data, proof certificates, and payload accounting distinct. Canonical
validity is established by theorems.

### Derived names state their semantics

```lean
namespace Layout

def superSampleCount (layout : Layout) : Nat :=
  layout.blockCount / layout.blocksPerSuper + 1

def superWidth
    (_layout : Layout) (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRank.machineWordBits shape.bpCode.length

def macroSize (layout : Layout) : Nat :=
  layout.blocksPerSuper * layout.blocksPerSuper

def macroSampleCount (layout : Layout) : Nat :=
  layout.blockCount / layout.macroSize + 1

def offsetWidth (layout : Layout) : Nat :=
  SuccinctRank.machineWordBits layout.macroSize

def levelCount (layout : Layout) : Nat :=
  layout.offsetWidth

def globalLevelCount (layout : Layout) : Nat :=
  SuccinctRank.machineWordBits layout.macroSampleCount

def blockAddressWidth (layout : Layout) : Nat :=
  SuccinctRank.machineWordBits layout.blockCount
```

The current names `SuperCountRaw` and `MacroCount` include a sentinel slot.
New names must say `SampleCount` or `SampleSlots`; they are not semantic
superblock counts.

### Validity and compact storage are different predicates

```lean
structure Layout.Valid
    (layout : Layout) (shape : Cartesian.CartesianShape) : Prop where
  blockSize_pos : 0 < layout.blockSize
  blocksPerSuper_pos : 0 < layout.blocksPerSuper
  relativeWidth_pos : 0 < layout.relativeWidth
  fullBlocks_fit :
    layout.blockCount * layout.blockSize <= shape.bpCode.length
  nextBlock_covers :
    shape.bpCode.length <
      (layout.blockCount + 1) * layout.blockSize
  superSpan_fits :
    2 * bpSuperblockSpan layout.blockSize layout.blocksPerSuper <
      2 ^ layout.relativeWidth
  blockOffset_fits :
    layout.blockSize < 2 ^ layout.relativeWidth

structure Layout.SummaryFits
    (layout : Layout) (shape : Cartesian.CartesianShape) : Prop where
  super_payload_fits :
    layout.superSampleCount * layout.superWidth shape <=
      sampledDirectoryOverhead
        canonicalBPRelativeSummarySuperSlots shape.size
  block_payload_fits :
    3 * (layout.blockCount * layout.relativeWidth) <=
      logLogSampledDirectoryOverhead
        canonicalBPRelativeSummaryBlockSlots shape.size
  relative_word_fits :
    layout.relativeWidth <=
      SuccinctRank.machineWordBits shape.bpCode.length

def Layout.CompactReady
    (layout : Layout) (shape : Cartesian.CartesianShape) : Prop :=
  layout.Valid shape /\
    layout.SummaryFits shape /\
    layout.macroSize <= layout.blockCount
```

`Valid` contains intrinsic layout/codec facts. `SummaryFits` says the
canonical summary representation has the intended payload budget and one-word
width. `CompactReady` requires both and adds the current two-level macro-size
condition.

No projection of `Layout` may branch on `SummaryFits` or `CompactReady`.

## Truthful Empty And Small Semantics

For the empty shape, the canonical layout has positive divisors and widths but
`blockCount = 0`. That zero is mathematical data, not an inactive marker.

For singleton and other small inputs, geometry remains total. When a query has
no nonempty interior range, that fact is proved from its bounds rather than
manufactured by erasing block geometry.

The sufficient-threshold theorem should be restated as a classifier:

```lean
theorem canonical_compactReady_or_below_threshold (shape) :
    (canonicalLayout shape).CompactReady shape \/
      shape.size < concreteBPRelativeRmmInteriorReadyThreshold
```

This theorem bounds the design space. It does not authorize dense all-pairs
answers, whole-payload structural scans, or a second public query algorithm.

## Compatibility Theorem Targets

U1 should prove:

```lean
@[simp] theorem canonicalLayout_blockSize ...
@[simp] theorem canonicalLayout_blocksPerSuper ...
@[simp] theorem canonicalLayout_blockCount ...
@[simp] theorem canonicalLayout_relativeWidth ...
@[simp] theorem canonicalLayout_superSampleCount ...
@[simp] theorem canonicalLayout_macroSize ...

theorem canonicalLayout_valid (shape) :
  (canonicalLayout shape).Valid shape

theorem canonicalLayout_summaryFits_iff_legacyActive (shape) :
  (canonicalLayout shape).SummaryFits shape ?
    canonicalBPRelativeMinMaxArgSummaryTableActive shape

theorem canonicalLayout_compactReady_iff_legacyReady (shape) :
  (canonicalLayout shape).CompactReady shape ?
    concreteBPRelativeRmmInteriorReady shape

theorem legacy_parameters_eq_canonical_of_summaryFits
    (hfits : (canonicalLayout shape).SummaryFits shape) :
  -- fieldwise equality with the current active-gated projections
  ...
```

Unconditional `rfl` lemmas are appropriate only for raw formulas and derived
quantities that are themselves ungated. Equality with the current canonical
summary table or directory is conditional on legacy Active/Ready because those
objects use active-gated parameters.

U1 should also prove the smallest behavioral agreement lemmas needed for the
existing Ready route, but it must not reimplement the final query.

## U1 Write Boundary

Preferred initial location: the existing
`RMQ/Core/SuccinctClose/RelativeSummary.lean` namespace surface.

`Layout.Valid.nextBlock_covers` needs
`canonicalBPRelativeSummaryBlockCountRaw_upper_cover`, which currently lives
downstream in `RelativeRmmMacro/LocalBPDecoder.lean`. U1 must relocate that
theorem, under the same declaration name, into `RelativeSummary.lean` before
using it. The proof depends only on the raw formulas and natural-number
division. Do not import the downstream decoder into `RelativeSummary.lean` or
leave a duplicate helper behind.

Do not move the raw formulas into a new file during U1. Moving them first would
combine semantic strengthening with import surgery and create a circular or
parallel API risk. A1 may later move the stable declarations to
`RelativeRmm/Layout.lean` while leaving compatibility imports and aliases.

U1 must not:

- alter `lcaCloseCosted` dispatch;
- add a packed fallback;
- lower or rename public cost constants;
- change headline aliases;
- remove zero-block compatibility code;
- add dense answer tables, synthetic events, or proof-only answers.

## U2 Question Left Open Deliberately

The first U2 attempt should totalize the existing compact hierarchy so small
inputs degenerate naturally through the same directory construction. A
separate counted packed implementation is acceptable only if a concrete formal
obstruction shows the hierarchy cannot cover the bounded small regime cleanly.

Thus the final interface may support implementation selection at construction
time, but U1 does not pre-commit the project to two algorithmic regimes.

Any U2 implementation must preserve:

- counted payload for every consumed cell;
- real charged reads and store agreement;
- successful-read flat-payload backing;
- machine-width address and operand bounds;
- exactness for empty, singleton, small, active-not-ready, and Ready inputs.

The current final surface already proves global store agreement, bounded machine
addresses, and successful counted-read backing. U2 may add component-specific
slot-in-range lemmas where they simplify the directory proof; it should not
misdescribe those global guarantees as absent.

## Architecture Guidance

Freeze these conceptual namespaces:

- `RMQ.SuccinctClose.RelativeRmm` for layout, summaries, and interior directory;
- `RMQ.SuccinctClose.BPClose` for the uniform close query;
- `RMQ.SuccinctFinal.Payload` for counted payload composition;
- `RMQ.SuccinctFinal.Execution` for address layout, stores, programs, traces,
  and supplied-store replay;
- `RMQ.SuccinctFinal.Cost` for modeled cost derivation;
- existing `RMQ.SuccinctClassic` for the list-facing API.

Do not freeze the scout's full fine-grained file tree. Split files only when
declaration closure and stable proof consumers justify a coherent unit. In
particular, avoid one-file-per-theorem-category fragmentation.

## Acceptance For U1

- Canonical layout projections are unconditional and computational.
- Every routing divisor and width has a positivity theorem.
- Counts retain exact zero semantics.
- `Valid`, `SummaryFits`, and `CompactReady` are separate.
- Legacy Active/Ready agreement is checked.
- Existing Ready-route behavior is unchanged through explicit agreement lemmas.
- No public query route, payload, cost, trace, or theorem claim changes.
- Targeted build, full `lake build`, `RMQPaper`, headline checks, hygiene,
  decision checks, and `git diff --check` pass.
