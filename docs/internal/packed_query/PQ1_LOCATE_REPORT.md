Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

This report concerns the bounded PQ1-L descriptor-location leaf. The lead owns
physical reading, arithmetic runtime-width safety and whole-query correctness.

## Identity and scope

- Handle: PQ1-L, returning metadata_width worker.
- Worktree: `C:/Users/poin/.codex/worktrees/a84a/RMQ`.
- Branch: `codex/fully-charged-packed-query-v1`.
- Assigned base: `b0af10d14121c7b11a7d3eb7cb1515c618a0da4b`.
- Governance: `4639223bc8130b0ef752270b5cbdd74325abcd60`.
- Skill preflight: PASS with required `rmq-proof-sprint`; actual runtime catalog
  `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`.
- Owned edits: Locate.lean; appended frame theorems in RegularLocate.lean and
  InteriorLocate.lean; PQ1_LOCATE_MATRIX.md; this report. Existing child source
  definitions and theorem signatures are unchanged. No staging or commits.
- Shared HEAD at final artifact verification equals the assigned base.
- SHA256 Locate.lean:
  `47c1dac194981053f785098484bdf651f3318dd505e8fd590000afab2227d18a`.
- SHA256 RegularLocate.lean:
  `34f7f2d14182e012d8a3a7928ca298d18a5eae32357f85ed772b3e34dc6bd0cd`.
- SHA256 InteriorLocate.lean:
  `f206225bd0cd3397e9325d6a36d35d9db05ce80e8a763eab600a08fdd9f4e575`.

## Construction and exact source proposition

`locateBlock base` has no size, shape, count, memory or endpoint parameter.
It tests the input segment in register `base`, keeping the input index at
`base+1`. A fixed outer comparison sends segment20 to eight interior cases;
the other branch compares against the fixed list `List.range 23`. Each regular
case copies four bank registers `58+4*segment` through `+3` and the input index
to the child block at `base+32`. Each interior case copies five bank registers
`150+5*interiorComponentIndex component` through `+4`, input index and register32
(BP width) to the interior child at `base+32`. These are literal source operands
after the finite source construction; runtime data never selects a register
through an indirect register-read instruction.

The generic theorem is:

```lean
locateBlock_source (base : Nat) (hb : 256 ≤ base)
  (memory : Memory) (regs : Registers) :
  let actual := (locateBlock base).eval memory ⟨regs, .running⟩
  LocationResult base
    (storedLogicalSpan regs (regs base) (regs (base + 1))) actual.final ∧
  actual.reads = [] ∧ LocateFrame base regs actual.final.regs
```

`LocationResult base span data` is exactly the conjunction of running status,
presence at base+2 (`0` for none, `1` for some), position at base+3 and length at
base+4 (both zero for none). `LocateFrame base before after` means
`∀ r, r < base+2 ∨ base+49 ≤ r → after r = before r`. This preserves both inputs,
the entire metadata bank16..189 and all other registers outside the declared
output/scratch interval. Both child frame lemmas preserve the existing child
source definitions and cover every register outside their documented writes.

`storedLogicalSpan` is the independent scalar specification: segment20 uses
`interiorComponents.findSome? (storedInteriorSpan regs index)`; other segments
below23 use the four stored fields in `regularSpan`; outside23 returns none.
Presence depends on stored word count. Thus a positive-count zero-bit sentinel
is present with length0, while an index at or beyond count is absent.

## Canonical same-object join and charged setup

`MetadataRegistersAgree shape regs` means exactly
`∀ i < 174, regs (16+i) = (metadata shape)[i]?.getD 0`.
The metadata-field theorems prove list-slot identities for every regular
descriptor field, every interior descriptor field and scalar BP-width index16.
They use the unchanged Allocation metadata definition and fixed-length flatten
indexing; no shape-specific data is inserted into executable state.

`storedRegularSpan_canonical` and `storedInteriorSpan_canonical` identify those
register specifications with LogicalSpan's `regularDescriptorSpan` and
`interiorDescriptorSpan`. The latter module's
`reviewerLogicalSpan_interior_descriptors` supplies the all-eight-component
classification equality, including its ceil-div/chunk-count bridge.
`storedLogicalSpan_canonical` then proves for every segment/index:

```lean
storedLogicalSpan regs segment index =
  reviewerLogicalSpan shape.size (longCount shape)
    (packedReviewerSparseCount shape) segment index
```

`locateBlock_canonical` rewrites the specification in the exact generic source
theorem; memory, source and evaluation stay identical. Shape may have any size;
the theorem has no readiness, nonzero-count, minimum-size or one-component
premise. `locate_canonical_requiredFacts` independently repeats every value,
status, read and frame projection rather than only a theorem name.

`setupLocateBlock base := .seq metadataSetupBlock (locateBlock base)` has size
1383. `buildMemory_setup_locate` starts with arbitrary registers, consumes
`buildMemory_setup` to obtain the actual charged bank, proves that setup
preserves the two high input registers, then invokes the same canonical locator.
Its result is the canonical span for the original inputs, receipts are exactly

```lean
(List.range 174).map
  (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩)
```

and all174 bank fields still agree with the metadata. The actual
`buildMemory_setup_locate_run` compiles this same sequence and obtains the same
values, receipts and bank, `steps ≤ 1383`, and final pc1383. Neither theorem
assumes initialized metadata registers or an expected output.

## Actual instruction runs and static fields

`locateBlock_size base` proves exact size1035. The standalone
`locateBlock_run` consumes Compiler's adequate fixed-budget `compile_run`: fuel
1035 gives the generic `LocationResult`, no reads, identical frame, steps≤1035
and final pc1035. The canonical version replaces only the scalar reference
using the metadata equality above. The complete hosted canonical type is:

```lean
locateBlock_canonical_hosted_run (base codeBase : Nat) (hb : 256 ≤ base)
  (shape : CartesianShape) (memory : Memory) (program : Program) (s : State)
  (hpc : s.pc = codeBase) (hs : s.status = .running)
  (hmeta : MetadataRegistersAgree shape s.regs)
  (host : HostedAt program codeBase ((locateBlock base).compileAt codeBase)) :
  ∃ used, used ≤ 1035 ∧
    let actual := run memory program used s
    LocationResult base (reviewerLogicalSpan shape.size (longCount shape)
      (packedReviewerSparseCount shape) (s.regs base) (s.regs (base + 1)))
      (Data.ofState actual.final) ∧ actual.reads = [] ∧
      LocateFrame base s.regs actual.final.regs ∧ actual.steps = used ∧
      actual.final.pc = codeBase + 1035
```

This is derived from `Compiler.Block.compile_correct` for the actual host
program and state. `locate_machine_requiredFacts` independently repeats the full
type with the expanded metadata and frame predicates. Host instructions after
the location segment are not executed by the existential segment fuel.

`locateBlock_writesOnly base` is a public syntactic inventory:
`(locateBlock base).WritesOnly (fun r => base+2 ≤ r ∧ r < base+49)`.
It covers dormant branches and arbitrary initial status. It is consumed by the
lead's PhysicalRead reader-frame proof.

`locateBlock_fieldsFit base width` needs only `256 ≤ base` and
`base+49 < 2^width`; it covers every source action encoding, operation tag,
register, immediate and branch tag. `locateBlock_compiled_fieldsFit` additionally
assumes `codeBase+1035 < 2^width` and concludes that every instruction in the
actual emitted program has every numeric encoding field below `2^width`.
These constants depend solely on the fixed syntax and register/code bases.
They do not prove that values computed during execution fit machine words;
that obligation remains in the separate safety work.

## Anti-vacuity and independent consumers

- `locate_non20_requiredFacts` states the actual source result using the four
  individually named stored descriptor registers.
- `locate_interior_requiredFacts` covers segment20 and the complete eight-case
  first-present specification.
- `locate_invalid_requiredFacts` and `locate_invalid_index_requiredFacts` prove
  absence with zero outputs for invalid segment and regular word index.
- `locate_empty_sentinel_requiredFacts` assumes only a valid non20 segment,
  index0, positive stored count and zero stored bit length; it proves actual
  output presence1, the stored bit base, length0, running status, no reads and
  the frame. It does not infer count from bit length.
- `locate_run_position_dependency` proves inequality of the actual base+3
  output registers when selected stored bit bases differ and each query selects
  index0 of a positive-count regular descriptor. This challenges the returned
  position itself; it cannot pass merely because logs differ.

No mutation campaign is claimed or assigned. The checked symbolic consumers
have no source-output, machine-output or desired-result premise. The reference
geometry is independently connected to canonical reviewer spans by LogicalSpan.

## Verification ledger

- Final Locate.lean artifact check: PASS, exit0, no warnings, 20.951 seconds;
  `.olean` and `.ilean` emitted with all final consumers and public write
  inventory. Direct Lean4.22.0 invocation uses only the private build tree
  (`LEAN_PATH=.lake/build/lib/lean`). All build-slot handoffs were explicit.
- Final InteriorLocate.lean cleanup artifact: PASS, exit0, no warnings,
  3.217 seconds. RegularLocate.lean's appended frame artifact passed its earlier
  narrow check without warnings; no later source edit was made there.
- Separate imported `.lake/build/PQ1LocateCheck.lean`: PASS, exit0, no warnings,
  1.369 seconds. It repeats the exact canonical source, hosted actual run,
  List Int charged setup-plus-location run, syntactic write inventory and full
  encoded-field propositions. Six independent scalar fixtures cover zero-bit
  sentinels, ragged regular/interior endings and out-of-range indices. Durable
  symbolic consumers remain in Locate.lean; this imported check is a private
  build artifact, not a mutation campaign.
- Axiom inspection of locateBlock_canonical_hosted_run,
  buildMemory_setup_locate_run, locateBlock_writesOnly and
  locate_run_position_dependency reports only `propext`, `Classical.choice`
  and `Quot.sound`.
- `git diff --check` over owned paths: PASS, exit0. A separate strict UTF-8 and
  trailing-whitespace scan covers all five owned files, including untracked
  files. Only Git's existing LF/CRLF notices were printed.
- Required global trust-footprint scan over RMQ and lakefile.toml: no matches
  for forbidden declarations or Mathlib import. Owned source scan for
  native_decide/Lean.ofReduceBool: no matches.
- Matrix integrity: all10 frozen requirement columns preserved byte-for-byte
  while updating evidence; all5 assigned requirement columns match the frozen
  prompt's UTF-8 bytes; all5 inherited texts match canonical completion-gate
  wording after unfolding its paragraph line breaks. No IDs changed or vanished.
- The initial dispatcher attempt expanded nested source evaluation; replacing
  it with generic branch/skip equations closed the proof without increasing the
  heartbeat limit. The first setup-composition attempt similarly expanded the
  174-load source; abstracting its intermediate Evaluation avoids that work.
- Fixed-width source checks exposed an overconservative copy-helper bound;
  changing its sufficient bound from destination+length+11 to
  destination+length+3 preserved the claimed locator register boundary.
- Full `lake build` and aggregate gate are skipped for this bounded leaf; the
  lead owns integration and broad certification.

## Proof digestion and design note for the lead

Conceptually, this closes the step from numbers already loaded into the counted
metadata bank to a logical word's exact old bit span. The program selects each
descriptor by fixed comparisons and copies its actual fields into ordinary
arithmetic blocks. The canonical proof explains what those numbers mean; it
does not participate in execution. The compiler proof shows that this result
belongs to a real bounded sequence of primitive transitions.

The live assumptions are the disjoint work-register base, running entry state,
proper code placement/hosting for machine theorems, and metadata agreement for
canonical locator-only theorems. The setup composition discharges metadata
agreement using the concrete builder's actual loads. No array-size assumption
is live. A skeptical graduate student should next ask whether every reachable
arithmetic intermediate fits the selected word width and whether the located
span is read and decoded with charged physical accesses. Those are the lead's
separate next joins, not claims of this location leaf.

Proposed design entry: fixed finite descriptor dispatch trades a larger constant
program (1035 instructions) for a transparent ordinary-register implementation.
The alternatives of runtime descriptor lookup or shape-specialized code would
hide either a primitive operation or nonuniform construction. Fixed branches
cover all23 regular cases and all8 interior components; stored word counts retain
empty sentinels. The cost is explicit syntax size and a49-register extent from
the work base. Every field, including dormant-branch operands, is statically
bounded. The lead should append this rationale to the shared design ledger
alongside its reader/controller composition. No ADD/process decision changed;
shared design/public-summary edits remain lead-owned.
