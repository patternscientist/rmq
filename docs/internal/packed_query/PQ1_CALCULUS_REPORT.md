Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

This declaration covers only the bounded PQ1-C primitive execution calculus
leaf commissioned in `PQ1_CALCULUS_PROMPT.md`. It does not declare the fully
charged packed-query capstone or the PQ1 roadmap node complete.

## Identity and ownership

- Worker: PQ1-C, physical execution calculus subagent.
- Worktree: `C:/Users/poin/.codex/worktrees/a84a/RMQ`.
- Branch: `codex/fully-charged-packed-query-v1`.
- Exact base/governance: `4639223bc8130b0ef752270b5cbdd74325abcd60`.
- Runtime project skills actually exposed: `rmq-audit-prompt`,
  `rmq-coordinator`, `rmq-proof-sprint`.
- Required local skill: canonical `.agents/skills/rmq-proof-sprint/SKILL.md`;
  completion gate and relevant failure modes read. Project preflight passed.
- Owned files: `RMQ/Core/WordRAM/Packed/Calculus.lean`,
  `docs/internal/packed_query/PQ1_CALCULUS_MATRIX.md`, this report.
- No edits to `Primitive.lean`, shared ledgers, original checkout, or audit
  checkout. No staging or commits; integration and commit identity are pending
  with the lead, as required by this leaf's checkout contract.
- Verified `Primitive.lean` SHA256:
  `5aff5c4e88267794cd3582a821d82a033d8364650ca1e353d7fd590877b52bf6`.
- Final `Calculus.lean` SHA256:
  `61c1bb9f5c14f4f40fb3f1f13d2d3a35967b8a90a3fa97639cd8d54ba0ac9f53`.

The completed [frozen evidence matrix](PQ1_CALCULUS_MATRIX.md) preserves the
ten assigned requirement texts. The calculus is independent of the lead's
simultaneous dense-packing and numeric-span work: its sole import is the
concrete primitive evaluator.

## Exact theorem surfaces

Every declaration below is in `RMQ.SuccinctFinal.PackedWordRAM`. `Memory` is
the primitive `List Nat` allocation; `Program` is its `List Instruction`;
`State`, `Transition`, `Run`, `execute`, `step`, and `run` are the definitions
from the unchanged `Primitive.lean` interface. There is no alternate evaluator.

Composition uses complete transitions, rather than independent receipt and
category lists:

```lean
def RunsTo (memory : Memory) (program : Program) (s s' : State)
    (transitions : List Transition) : Prop :=
  run memory program transitions.length s = ⟨s', transitions⟩

theorem run_add (memory : Memory) (program : Program) (a b : Nat) (s : State) :
    run memory program (a + b) s =
      let first := run memory program a s
      let second := run memory program b first.final
      ⟨second.final, first.transitions ++ second.transitions⟩

theorem RunsTo.refl (memory : Memory) (program : Program) (s : State) :
    RunsTo memory program s s []

theorem RunsTo.trans {memory : Memory} {program : Program}
    {s₁ s₂ s₃ : State} {ts₁ ts₂ : List Transition}
    (h₁ : RunsTo memory program s₁ s₂ ts₁)
    (h₂ : RunsTo memory program s₂ s₃ ts₂) :
    RunsTo memory program s₁ s₃ (ts₁ ++ ts₂)

theorem RunsTo.of_step {memory : Memory} {program : Program} {s : State}
    {t : Transition} (h : step memory program s = some t) :
    RunsTo memory program s t.after [t]

theorem RunsTo.instruction {memory : Memory} {program : Program} {s : State}
    {i : Instruction} (hrunning : s.status = .running)
    (hfetch : program[s.pc]? = some i) :
    RunsTo memory program s (execute memory i s).1
      [⟨s, i, (execute memory i s).1, (execute memory i s).2⟩]

theorem run_add_of_halted (memory : Memory) (program : Program) (a b : Nat)
    (s : State) (value : Nat)
    (h : (run memory program a s).final.status = .halted value) :
    run memory program (a + b) s = run memory program a s

theorem RunsTo.fuel_extension {memory : Memory} {program : Program}
    {s s' : State} {ts : List Transition} {value : Nat}
    (h : RunsTo memory program s s' ts) (halted : s'.status = .halted value)
    (extra : Nat) :
    run memory program (ts.length + extra) s = ⟨s', ts⟩
```

Accounting is an exact partition of the actual transition log. It is not a
native runtime assertion or a constant query-budget theorem:

```lean
def Run.categoryCount (r : Run) (c : Category) : Nat := r.categories.count c

theorem Run.steps_eq_categories_length (r : Run) :
    r.steps = r.categories.length

theorem Run.steps_partition (r : Run) :
    r.steps = r.categoryCount .memoryRead + r.categoryCount .registerWrite +
      r.categoryCount .arithmetic + r.categoryCount .comparison +
      r.categoryCount .branch + r.categoryCount .control

theorem run_steps_le_fuel (memory : Memory) (program : Program) (fuel : Nat)
    (s : State) : (run memory program fuel s).steps ≤ fuel
```

Positional provenance is universal in transition index, memory, program, fuel
and initial state. In particular, repeated equal receipts do not collapse:

```lean
theorem run_transition_at {memory : Memory} {program : Program} {fuel : Nat}
    {s : State} {k : Nat} {t : Transition}
    (h : (run memory program fuel s).transitions[k]? = some t) :
    t.before = (run memory program k s).final ∧
      step memory program t.before = some t

theorem run_transition_spec {memory : Memory} {program : Program} {fuel : Nat}
    {s : State} {k : Nat} {t : Transition}
    (h : (run memory program fuel s).transitions[k]? = some t) :
    t.before = (run memory program k s).final ∧
      t.before.status = .running ∧
      program[t.before.pc]? = some t.instruction ∧
      execute memory t.instruction t.before = (t.after, t.receipt)

theorem execute_receipt {memory : Memory} {i : Instruction} {s : State}
    {receipt : Receipt} (h : (execute memory i s).2 = some receipt) :
    ∃ dst addrReg, i = .load dst addrReg ∧
      receipt.address = s.regs addrReg ∧ receipt.reply = memory[receipt.address]?

theorem run_read_at {memory : Memory} {program : Program} {fuel : Nat}
    {s : State} {k : Nat} {t : Transition} {receipt : Receipt}
    (h : (run memory program fuel s).transitions[k]? = some t)
    (hr : t.receipt = some receipt) :
    t.before = (run memory program k s).final ∧
      t.before.status = .running ∧
      program[t.before.pc]? = some t.instruction ∧
      execute memory t.instruction t.before = (t.after, t.receipt) ∧
      ∃ dst addrReg, t.instruction = .load dst addrReg ∧
        receipt.address = t.before.regs addrReg ∧
        receipt.reply = memory[receipt.address]?
```

Dynamic memory agreement is proved by induction on the first actual run.
The proof obtains equality of the fetched instruction execution from agreement
on that instruction's receipt, then applies induction to the actual suffix.
No legacy static-footprint result is imported or used:

```lean
theorem run_eq_of_agree (memory memory' : Memory) (program : Program) (fuel : Nat)
    (s : State)
    (h : ∀ receipt ∈ (run memory program fuel s).reads,
      memory'[receipt.address]? = memory[receipt.address]?) :
    run memory' program fuel s = run memory program fuel s

theorem run_observations_eq_of_agree (memory memory' : Memory) (program : Program)
    (fuel : Nat) (s : State)
    (h : ∀ receipt ∈ (run memory program fuel s).reads,
      memory'[receipt.address]? = memory[receipt.address]?) :
    (run memory' program fuel s).result = (run memory program fuel s).result ∧
      (run memory' program fuel s).steps = (run memory program fuel s).steps ∧
      (run memory' program fuel s).categories = (run memory program fuel s).categories ∧
      (run memory' program fuel s).reads = (run memory program fuel s).reads
```

The agreement premise uses event membership solely to quantify the set of
numeric lookup equalities needed for replay. The separate provenance theorem
retains occurrence indices and complete transitions. Failed replies participate
in the same lookup equality; replacing `none` by `some value` violates it.

## Direct consumers and boundary challenges

All consumers are kernel-checked theorems in `CalculusExamples`, inside the
same module. Their scalar expectations were literal specifications:

| Consumer | Checked conclusion and dependency |
| --- | --- |
| `successfulLoad` | Loading cell 0 from `[7]`, then halting on its destination, returns `some 7`; receipts are `[(0,some 7)]`, steps are 2, categories are `[memoryRead,control]`. |
| `failedLoad` | The same program on `[]` returns no result and faults, with receipt `[(0,none)]` and exactly one step despite fuel 2. |
| `failedLoad_positional` | Projects `run_read_at` for the actual failed occurrence at transition 0, retaining prefix, running pre-state, fetch, execute equality, load operands and `none` backing. |
| `repeatedLoads` | Two explicit loads of cell 0 return `some 7` and emit two equal receipts. |
| `repeatedLoad_positions` | Uses `run_read_at` to pin those occurrences to indices 0 and 1, prefix states with PCs 0 and 1. |
| `suppliedMemoryAgreement` | Uses `run_eq_of_agree` to prove full run equality for `[7]` and `[7,99]`; the untouched suffix may differ. |
| `loadedValue_changes_result` | The returned `Option Nat` for `[7]` differs from that for `[8]`. This checks result projection, not merely log inequality. |
| `failedAddress_not_agreement` | Negates exactly the universally quantified agreement premise of `run_eq_of_agree` for `[]` versus `[7]`, using the actual failed receipt. There is no stronger proxy predicate. |
| `composedLoadAndHalt` | Consumes `RunsTo.instruction`, `RunsTo.trans`, and `RunsTo.fuel_extension` to return `some 7` at fuel `2+extra` for every extra fuel; consumes `Run.steps_partition` for that same run. |

These are stable checked source fixtures. No exhaustive source-mutation
campaign, mutation runner, measured universal budget, or whole-RMQ validation
claim is made. Replay-registry requirements therefore do not acquire an
unimplemented harness obligation in this leaf.

## Verification and independent review

All Lean runs were direct, narrow module checks under the lead's serialized
build-slot protocol. No wrapper timeout, surviving child, aggregate build,
unchanged expensive retry, or mutable shared-cache write occurred.

```powershell
$env:LEAN_PATH = Join-Path $PWD '.lake/build/lib/lean'
& 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe' `
  -o .lake/build/lib/lean/RMQ/Core/WordRAM/Packed/Calculus.olean `
  RMQ/Core/WordRAM/Packed/Calculus.lean
```

| Check | Outcome |
| --- | --- |
| Canonical project skill preflight at the exact governance ref | PASS, with actual runtime catalog recorded above. |
| Initial draft elaboration | Exit 1 in 6.14s; diagnosed local let-reduction rewrites, a tactic case-pattern syntax error, and a dependent consumer rewrite. No timeout. |
| Repaired core and direct consumers | Exit 0 in 7.34s, no warnings. |
| Final source including `failedLoad_positional` | Exit 0 in 5.49s, no warnings; tool command chunk `78bcf8`. Final SHA256 is recorded above; no subsequent Lean edits. |
| Scoped forbidden-token/import scan and `native_decide`/`Lean.ofReduceBool` scan | No matches in `Calculus.lean`. |
| Owned-file `git diff --check` and no-index checks for new files | No whitespace defects. New-file no-index comparison returns 1 because files differ from `/dev/null`; Git reported only the normal LF-to-CRLF conversion notice. |
| Frozen requirement-column preservation | All ten unique IDs retained their exact requirement-column strings during evidence updates. |
| Independent read-only source audit by `memory_inventory` | No actionable discrepancy at final source SHA256. The reviewer independently checked actual composition, occurrence provenance, failed replies, agreement induction direction and hygiene. Its pending-final-compile caveat was resolved by the final successful check above. |

The lead owns scoped integration commits, the exact committed-range whitespace
check, strict design-policy check, broad gates, later block/capstone consumers,
and the required fresh blind exact-commit audit of the complete public target.
Those are not falsely represented by this local source review.

## Proposed design-decision entry for lead append

**Title:** Preserve complete primitive transitions in the packed execution calculus.

**Context.** The packed-query construction must compose charged primitive
blocks and establish the source of each physical read, including repeated
equal events and failures. Separate event lists or event-value membership
cannot establish which invocation, pre-state or instruction produced a read.

**Decision.** `RunsTo` records the exact `Transition` list emitted by the
existing primitive evaluator at fuel equal to that list's length. `run_add`
composes these lists and final states directly. A transition-index theorem
identifies the producing prefix state, fetched instruction and exact execution;
receipt inversion then recovers the load operands and numeric lookup. Dynamic
memory agreement follows execution induction and includes absent replies.

**Alternatives rejected.** Separate hand-authored receipt/category schedules
would require an additional identity bridge and invite synthetic observations.
A `List.Mem`-only provenance theorem would erase repeated-event positions.
Deriving agreement through an older static footprint would leave the wrong
execution theorem load-bearing. These alternatives are unnecessary because
the primitive evaluator already retains sufficient transition information.

**Consequences.** Concrete blocks can compose without changing evaluator or
store arguments. The exact six-category partition refers to those same
transitions. Transition and pre-state records remain proof observations;
this choice alone proves no allocation, scratch-space, word-width or constant
query-budget bound. The whole-query lead must establish those properties for
its one canonical builder/program and consume this calculus there.

**Evidence.** `RMQ.SuccinctFinal.PackedWordRAM.run_add`, `RunsTo.trans`,
`run_read_at`, `run_eq_of_agree`, and the checked failed/repeated-load consumers
at the source identity above. Unqualified names here use the same
`RMQ.SuccinctFinal.PackedWordRAM` namespace.

No workflow/process rule is changed by this leaf, so no workflow-ledger entry
is proposed. The main design ledger was deliberately left to the lead's
coordinated append as required by the disjoint ownership contract.

## Proof digestion and live assumptions

Conceptually, one run now carries its own compositional proof interface. A
block proof can state its exact transition segment, compose with a successor,
and retain the exact pre-state and physical reply of every load. Memory
agreement is established from those dynamic replies rather than from a
separately selected set of possible accesses.

In plain English, breaking execution into proved pieces does not lose which
instructions ran or where each read came from. A failed read is still an
attempted read. Two identical reads remain two occurrences. Changing only
unread memory cannot alter the execution or answer, while a changed loaded
value can alter the answer.

The live assumptions are precisely the primitive evaluator definitions,
ordinary finite lists for program/memory, natural-number registers, and the
explicit hypotheses shown in the theorem types. There are no new proof trust
primitives, semantic answers, machine-width hypotheses, or RMQ reference
callbacks in this module. Natural representatives do not by themselves prove
finite-width machine legality, and supplied fuel does not by itself prove an
input-independent adequate query budget.

A skeptical graduate student should next inspect the lead's actual block
proofs: do they instantiate these theorems with the exact counted allocation,
do their output registers depend on these reads, and do they establish one
adequate constant instruction budget and global width bound for that same
execution? Those are the downstream whole-query obligations; all assigned
generic calculus obligations are discharged here.
