Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

This declaration concerns the bounded PQ1-U metadata-setup leaf. Whole-query
correctness and all intermediate machine-width obligations remain with the lead.

## Identity

- Handle: PQ1-U, returning metadata_width worker.
- Worktree: `C:/Users/poin/.codex/worktrees/a84a/RMQ`.
- Branch: `codex/fully-charged-packed-query-v1`.
- Assigned base and shared HEAD at verification:
  `9e2720b991e203d22a2787abf66dbfb9888088fb`.
- Governance: `4639223bc8130b0ef752270b5cbdd74325abcd60`.
- Preflight: PASS; actual catalog
  `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`; required
  `rmq-proof-sprint`.
- Owned files: Setup.lean, PQ1_SETUP_MATRIX.md, this report. No staging, commits,
  shared ledger edits, prior-module modifications or branch switching.
- Setup.lean SHA256:
  `9867db613ad3347f509022545e7b509c3ebdbc8d1e0167b8acd0a351d81fbd42`.

## Source and same-object chain

`metadataSetupBlock` is the closed `metadataSetupFrom 0 174` source.
`metadataSetupBlock_compile base` proves its emitted program equals

```lean
((List.range 174).map fun i =>
  [Instruction.constant 6 i, Instruction.load (16 + i) 6]).flatten
```

for every base. It has size 348. Thus every field performs its own constant
address instruction and raw memory load into registers 16 through 189; register
6 is scratch. Neither n nor shape nor endpoint values specialize the source.

The generic `metadataSetupBlock_eval` assumes only a running source Data and
`174 ≤ memory.length`. It concludes: final status running; destination `16+i`
equals `(memory[i]?).getD 0` for every i<174; register6=173; every register outside
6 and 16..189 is unchanged; receipts are exactly
`(List.range 174).map (fun i => ⟨i, memory[i]?⟩)`.

`shapeMemory_metadata_prefix` and `buildMemory_metadata_prefix` prove that every
one of these positions is the corresponding concrete metadata field.
`shapeMemory_setup` and `buildMemory_setup` consume those equalities in the same
evaluation. No header-fit or preinitialized metadata assumption is used.
`shapeMemory_setup_registers_fit` consumes Width's unconditional stored-word
bound for that allocation and preserves fit in every register outside the
written bank. The List Int form uses the same builder and exact shape-size
identity.

## Exact actual-run theorem

All declarations are in `RMQ.SuccinctFinal.PackedWordRAM`. The canonical theorem
has the following complete type:

```lean
buildMemory_setup_run (xs : List Int) (s : State)
  (hpc : s.pc = 0) (hs : s.status = .running)
  (hregs : ∀ r, s.regs r < 2 ^ wordWidth xs.length) :
  let actual := run (buildMemory xs) (metadataSetupBlock.compileAt 0) 348 s
  actual.final.status = .running ∧
  (∀ i < 174, actual.final.regs (16 + i) =
    ((metadata (SuccinctClassic.cartesianShape xs))[i]?).getD 0) ∧
  actual.final.regs 6 = 173 ∧
  (∀ r, r ≠ 6 → (r < 16 ∨ 190 ≤ r) → actual.final.regs r = s.regs r) ∧
  actual.reads = (List.range 174).map
    (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ∧
  actual.steps ≤ 348 ∧ actual.final.pc = 348 ∧
  (∀ r, actual.final.regs r < 2 ^ wordWidth xs.length)
```

It consumes `Compiler.Block.compile_run`, including its derived adequacy and
fixed syntax budget. `setup_run_requiredFacts` independently repeats this exact
type, while `setup_source_requiredFacts` independently repeats every canonical
source proposition.

`buildMemory_setup_hosted_run` additionally takes any program, base, state
with pc=base, and `HostedAt program base (metadataSetupBlock.compileAt base)`.
Through `Compiler.Block.compile_correct` it derives `∃ used, used≤348` and
all the same data/frame/receipt/register-fit conclusions for
`run (buildMemory xs) program used s`; its step count is exactly used and its
final PC is base+348. The used count is produced by compiler adequacy, not
assumed by the caller. This is the consumer for placing setup behind the guard.

`metadataSetupBlock_compiled_fieldsFit n base` proves every encoded instruction
tag, register identifier and address immediate fits `wordWidth n`, for every
compilation base. These instructions contain no encoded branch targets;
placement-PC representability for a hosted segment remains a whole-program
obligation.

## Positional backing and value dependency

`metadataSetupBlock_run_field_receipt` proves, for every i<174 in a sufficiently
long memory, both the actual installed value and
`actual.reads[i]? = some ⟨i, memory[i]?⟩`. This preserves receipt position and
physical lookup identity, rather than only membership.

The checked counterfactual `metadataSetupBlock_run_value_dependency` uses two
sufficiently long memories and the same initial state. If their actual loaded
values at i differ, the actual final destination `16+i` differs. Its predicate
is the same destination equality specified by the main generic run theorem;
the proof does not substitute an inequality of enclosing trace records.
This is a formal universally quantified dependency theorem, not a claimed
mutation campaign.

## Verification

- Initial narrow check: 1.606s, four local scratch/arithmetic/static-fit goals.
  Repaired those proofs before retrying; no timeout or repeated unchanged run.
- Second narrow check: 1.607s, exit0; removed two unused simp arguments.
- Final artifact-producing check: exit0, no warnings, 2.0893283s. Emitted
  Setup.olean and Setup.ilean in the private worktree cache.
- Separate importing consumer: complete source and primitive theorem types
  restated independently; exit0, 1.8286152s.
- Axiom inventory of `setup_source_requiredFacts`, `setup_run_requiredFacts`,
  `buildMemory_setup_hosted_run` and `metadataSetupBlock_run_value_dependency`:
  each uses exactly `propext`, `Classical.choice`, `Quot.sound`.
- Empty source allocation and arbitrary singleton primitive PC consumers passed
  in the source module without materializing expensive preprocessing examples.
- Owned proof-trust/hygiene scan: no forbidden token or Mathlib/native-decision
  matches. Shared `git diff --check` passed. Owned whitespace and frozen-row
  checks are in the matrix ledger.
- No broad Lake/aggregate gate or mutation campaign: the lead owns final
  integration and committed-range/strict-design checks. Every Lean process
  used the explicitly coordinated single build slot.

## Proof digestion and proposed design entry

The key proof is induction on a finite list of ordinary constant/load pairs.
Its induction invariant preserves the bank values already installed, the exact
receipt order, the scratch address and every outside register. The compiler
transports this independent source fact into actual primitive transitions.

In plain English, the machine now obtains its entire concrete geometry bank
through paid memory reads. It cannot receive a different header value while
keeping the corresponding destination unchanged under the proved execution.
Canonical word fit comes from the same allocation's Width theorem.

Live assumptions are a running input state, sufficient memory for the generic
lemma, initial register fit for the post-fit conclusion, and a matching hosted
code segment for the placement theorem. Canonical allocation length and all
metadata-word fits are proved, not assumptions. Whole-query register
intermediates, guard behavior and hosted PC widths remain lead-owned.

A skeptical graduate student should inspect how the guarded whole program
uses this bank, how later code preserves the reserved registers, and how the
hosted segment joins to the rest of the actual execution.

Proposed shared design-ledger append: record the reserved bank16..189, scratch6,
fixed 174-pair/348-instruction syntax, and the source-to-Compiler-to-canonical-
allocation identity chain. Explain that a batch-load instruction or prefilled
geometry registers would hide work or introduce uncounted setup, while the
chosen finite source exposes every physical attempt. Cite Setup.lean's hosted
run, positional receipt and value-dependency theorems. This worker did not edit
the shared ledger concurrently.
