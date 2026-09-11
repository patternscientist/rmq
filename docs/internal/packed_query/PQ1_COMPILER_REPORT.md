Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

This is the bounded PQ1-T generic structured-assembly compiler leaf. It does
not declare the whole packed-query capstone or PQ1 roadmap node complete.

## Identity and delivered files

- Worker: PQ1-T, returning `primitive_calculus` subagent.
- Worktree: `C:/Users/poin/.codex/worktrees/a84a/RMQ`.
- Branch: `codex/fully-charged-packed-query-v1`.
- Exact assigned base: `9e2720b991e203d22a2787abf66dbfb9888088fb`.
- Workflow governance: `4639223bc8130b0ef752270b5cbdd74325abcd60`.
- Actual runtime project skills: `rmq-audit-prompt`, `rmq-coordinator`,
  `rmq-proof-sprint`. Canonical proof-sprint skill, completion gate and relevant
  failure modes were applied; the required project-skill preflight passed.
- Owned changes: `RMQ/Core/WordRAM/Packed/Compiler.lean`,
  `PQ1_COMPILER_MATRIX.md`, and this report.
- No staging, commits, shared-ledger writes, original-checkout edits or source
  interface changes. Integration commit and coordinator acceptance are pending
  with the lead as required by the checkout contract.
- Final compiler SHA256:
  `0c527f0cd9db8be2860bcf1815826bbeed05e22d3660e450285f70dddfaeff60`.

The completed [acceptance matrix](PQ1_COMPILER_MATRIX.md) records all eleven
assigned rows. Exact requirement texts and unique IDs were checked against the
frozen prompt and inherited completion-gate text after evidence updates.

The unchanged imported source identities are:

| File | SHA256 |
| --- | --- |
| `Primitive.lean` | `5aff5c4e88267794cd3582a821d82a033d8364650ca1e353d7fd590877b52bf6` |
| `Calculus.lean` | `61c1bb9f5c14f4f40fb3f1f13d2d3a35967b8a90a3fa97639cd8d54ba0ac9f53` |
| `Structured.lean` | `5cde17b16464526272a4cac619a83cf7015d6d5db2725839ca26cf6f9d48198c` |

## Exact interfaces and object identities

All names below are in `RMQ.SuccinctFinal.PackedWordRAM.Structured`; primitive
names resolve to the existing parent namespace. The compiler imports the
unchanged `Structured.lean`, whose `Block.eval` is an independent compositional
source semantics with registers/status and no program counter. The evaluator
does not invoke compiled code. `Block.compileAt` emits the existing primitive
instruction vocabulary without receiving memory or query endpoints.

Code placement preserves exact indexed fetches:

```lean
def HostedAt (program : Program) (base : Nat) (code : Program) : Prop :=
  ∀ i, i < code.length → program[base + i]? = code[i]?

theorem Block.compile_length (block : Block) (base : Nat) :
    (block.compileAt base).length = block.size

theorem Block.compile_repeat_succ (count : Nat) (body : Block) (base : Nat) :
    (Block.repeat (count + 1) body).compileAt base =
      body.compileAt base ++ (Block.repeat count body).compileAt (base + body.size)
```

`HostedAt.self`, `head`, `append`, `append_left`, and `append_right` prove the
corresponding exact hosting facts. Both sequence and finite-repeat compilation
consume these same list-segment facts; empty bodies need no positive-offset
or PC-injectivity assumption.

The internal proof preserves the actual transition segment:

```lean
def Realizes (memory : Memory) (program : Program) (s : State)
    (expected : Evaluation) (finish budget : Nat) : Prop :=
  ∃ final transitions,
    RunsTo memory program s final transitions ∧
    Data.ofState final = expected.final ∧
    transitions.filterMap (·.receipt) = expected.reads ∧
    transitions.length ≤ budget ∧
    (final.status = .running → final.pc = finish)

theorem Block.compile_realizes (memory : Memory) (program : Program) (block : Block)
    (base : Nat) (s : State) (hpc : s.pc = base)
    (host : HostedAt program base (block.compileAt base)) :
    Realizes memory program s (block.eval memory (Data.ofState s))
      (base + block.size) block.size
```

`Realizes` is a proof proposition with witnesses constrained by the concrete
`RunsTo` execution equality. It is not executable proof-carried routing or a
source-provided answer. The public theorem unfolds that exact execution:

```lean
theorem Block.compile_correct (memory : Memory) (program : Program) (block : Block)
    (base : Nat) (s : State) (hpc : s.pc = base)
    (host : HostedAt program base (block.compileAt base)) :
    ∃ used, used ≤ block.size ∧
      Data.ofState (run memory program used s).final =
        (block.eval memory (Data.ofState s)).final ∧
      (run memory program used s).reads = (block.eval memory (Data.ofState s)).reads ∧
      (run memory program used s).steps = used ∧
      ((run memory program used s).final.status = .running →
        (run memory program used s).final.pc = base + block.size)
```

No result, read-backing, budget-adequacy, initial-running, or successful-memory
premise is supplied. The only execution-placement premises are the displayed
initial PC and exact hosting relation. The proof handles all constructors and
all memory lists, including missing physical cells.

Static encoded-field fit is constructor-exhaustive:

```lean
def Block.FieldsFit (width : Nat) : Block → Prop
  | .skip => True
  | .action op => op.instruction.Fits width
  | .exit src => (Instruction.halt src).Fits width
  | .seq a b => a.FieldsFit width ∧ b.FieldsFit width
  | .ifZero c a b => (Instruction.branchZero c 0).Fits width ∧
      (Instruction.jump 0).Fits width ∧ a.FieldsFit width ∧ b.FieldsFit width
  | .repeat _ body => body.FieldsFit width

theorem Block.compile_fits (block : Block) (width base : Nat)
    (fields : block.FieldsFit width) (bound : base + block.size < 2 ^ width) :
    ∀ instruction ∈ block.compileAt base, instruction.Fits width
```

`Instruction.Fits` quantifies over the exact serialized encoding, including
operation tags, arithmetic subtags, registers, immediate constants and control
targets. The proof derives resolved target bounds from `base+size`, and bounds
every expanded repetition offset. Both branch arms are covered even when one
is dormant. Requiring the body predicate for count-zero repetition is a
conservative sufficient condition, not an iff characterization of emitted code.
This theorem asserts no runtime register, arithmetic-result or data-address
safety.

The standalone and whole-program consumers use fixed fuel, derived from syntax:

```lean
theorem Block.compile_run (memory : Memory) (block : Block) (s : State)
    (hpc : s.pc = 0) :
    Data.ofState (run memory (block.compileAt 0) block.size s).final =
      (block.eval memory (Data.ofState s)).final ∧
    (run memory (block.compileAt 0) block.size s).reads =
      (block.eval memory (Data.ofState s)).reads ∧
    (run memory (block.compileAt 0) block.size s).steps ≤ block.size ∧
    ((run memory (block.compileAt 0) block.size s).final.status = .running →
      (run memory (block.compileAt 0) block.size s).final.pc = block.size)

theorem Block.compile_with_halt (memory : Memory) (block : Block) (output : Nat)
    (s : State) (hpc : s.pc = 0) :
    let source := block.eval memory (Data.ofState s)
    let program := block.compileAt 0 ++ [Instruction.halt output]
    let actual := run memory program (block.size + 1) s
    Data.ofState actual.final = ((Block.exit output).eval memory source.final).final ∧
    actual.result = (match source.final.status with
      | .running => some (source.final.regs output)
      | .halted value => some value
      | .fault => none) ∧
    actual.reads = source.reads ∧ actual.steps ≤ program.length
```

For standalone normal completion, the final PC is exactly the first address
after its compiled program, so further fuel cannot fetch another instruction.
Halted/faulted states also cannot step. This proves the fixed-budget corollary
from the existential exact segment. Appending the source exit and applying
that corollary proves the displayed whole-program statement, including the
halt instruction's cost and preservation of earlier halt/fault outcomes.

## Composition chain and direct consumers

The complete local chain is:

```text
Structured.Block / independent Block.eval
  -> exact compileAt placement and finite expansion
  -> compile_realizes: concrete RunsTo transition segments
  -> compile_correct: source-equal actual state, ordered reads, exact used steps
  -> compile_run: fixed full compiled-size fuel
  -> compile_with_halt: output/result, reads and whole-program budget
```

All arrows preserve the same source block, program list, memory argument,
initial state and actual primitive evaluator. No sibling memory, replayed
receipt list or semantic answer is supplied to the primitive machine.

`CompilerConsumers.compile_correct_expectedType`,
`compile_fits_expectedType`, and `compile_with_halt_expectedType` restate and
consume the complete expected types above. These types are written independently
of the referenced declarations, rather than inferred from their current types.

The literal kernel consumers supplement the universal proofs:

| Consumer | Actual checked boundary |
| --- | --- |
| `overwrittenOperand_result` | Constant 4 then `add r1 r1 r1` returns `some 8`, preserving read-before-write operands. |
| `zero_branch` / `nonzero_branch` | Branch condition is overwritten in the selected arm; results are 9/8 with actual steps 3/4 after output halt. |
| `empty_branches` | Both empty arms remain correctly charged: zero path 2 steps, nonzero path 3, including output halt. |
| `repeat_zero` | Zero copies of an exiting body do not execute it; appended halt returns 3 in one step. |
| `repeat_empty` | Three copies of an empty body have zero code/steps and preserve data. |
| `repeated_receipts` | Three explicit loads preserve three equal ordered receipts `(0,some 7)`, return 7, and use four steps with halt. |
| `missing_load_termination` | First load from `[]` faults, preserves `(0,none)`, skips a later constant/repetitions/halt and uses one step. |
| `early_exit` | A source exit preserves its value 3 and skips a following missing load and appended halt; no reads, one step. |
| `initially_halted` / `initially_faulted` | Existing terminal status is preserved with zero steps. |
| `branch_code_fits` | The actual branch program's complete encoding fits width 4. |
| `tiny_exit_rejected` | The exact field-fit predicate rejects exit tag 8 at width 1. |
| `dormant_branch_rejected` | An oversized operand in a dormant arm is rejected. |
| `arithmetic_tag_rejected` | Arithmetic subtag 9 is rejected at width 3 even with register IDs zero. |

These are stable source theorems with literal expected values. No exhaustive
mutation campaign or mutation replay registry is claimed.

The active downstream span worker additionally reported checked consumers in
`SpanAssembly.lean`: `spanBlock_machine` consumes `compile_correct` for the
22-position span block, preserving exact used steps/reads/frame/continuation;
`spanRun_correct` consumes `compile_run` for the 23-position span routine and
proves decoded result, terminal status, exact reads, frame and steps at most 23.
`spanRun_inputs` discharges its register inputs. These downstream checks were
reported by the disjoint span owner; the generic compiler candidate does not
stand in for whole-PQ1 acceptance.

## Verification and review

The final command used only the local independent output tree:

```powershell
$env:LEAN_PATH = Join-Path $PWD '.lake/build/lib/lean'
& 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe' `
  -o .lake/build/lib/lean/RMQ/Core/WordRAM/Packed/Compiler.olean `
  -i .lake/build/lib/lean/RMQ/Core/WordRAM/Packed/Compiler.ilean `
  RMQ/Core/WordRAM/Packed/Compiler.lean
```

| Check | Result |
| --- | --- |
| Governance/role preflight | PASS at assigned base with actual runtime catalog. |
| Core universal compilation, hosting/length and static fit | Exit 0, no warnings, 2.86s. |
| Public exact-segment, fixed-budget and appended-halt corollaries | Exit 0, no warnings, 2.31s. |
| Final complete module, all full expected-type and literal consumers, `.olean`/`.ilean` emission | Exit 0, no warnings, 1.93s; command chunk `603cb4`; source SHA256 above. |
| Scoped trust/import and native-decision scans | No forbidden-token, Mathlib, `native_decide` or `Lean.ofReduceBool` matches in `Compiler.lean`. |
| Imported-interface preservation | Primitive/Calculus/Structured final hashes exactly match preflight hashes. |
| Frozen matrix text/ID check | All eleven unique requirement texts match their frozen prompt/gate text. |
| Owned whitespace checks | No whitespace defects under `git diff --check` and no-index checks for new files. Git's LF-to-CRLF notices are line-ending conversion notices; no-index status 1 denotes a new file differing from `/dev/null`. |

Development failures were short local elaboration failures (normalizing offsets,
reserved constructor syntax, a tactic alias unavailable in Lean/Std, and a
duplicate namespace end), followed by source repairs. No expensive full build,
timeout, surviving child, unchanged timed-out retry, mutation campaign or shared
read-only-cache write occurred. A crossed build-slot handoff was identified and
the workers switched to explicit direct handoffs; all final checks were
serialized and no process remains from this worker.

An independent read-only source-contract review by `memory_inventory` found no
semantic impossibility and identified the stopped-state, empty-body, conditional
jump and instruction-tag boundaries. Each is implemented and covered above.
This was an architecture/contract review, not a fresh blind exact-commit audit
of the final source. The latter is not assigned to this generic leaf; the lead
owns coordinator acceptance, integration checks and the complete public
capstone's required audit.

No broad gate was run because this is a narrow additive compiler leaf. The
lead owns `design_decision_check.ps1 -Strict -Base
4639223bc8130b0ef752270b5cbdd74325abcd60`, exact committed-range whitespace
checks after integration, and whole-query/public certification.

## Proposed design entry for the lead's coordinated append

**Title:** Compile fixed structured assembly with exact primitive segments.

**Context.** The packed query needs reusable scalar source blocks with branches
and bounded repetition, while the final cost claim must concern the physical
primitive program. The source evaluator deliberately omits PCs and has no
asserted unit-cost runtime. Its specification alone cannot certify primitive
execution, instruction count or code addressability.

**Decision.** Keep `Structured` unchanged and prove its compiler by syntax
induction. Exact hosting locates each compiled segment, including every expanded
repeat copy. `Realizes` retains a `RunsTo` transition segment, state equality,
ordered receipt equality, a static size bound and the running continuation PC.
Sequential composition stops immediately after halt/fault; nonzero arms execute
the forwarding jump only when still running. A standalone final-PC/no-step
argument upgrades the exact segment to the fixed compiled-size budget, and a
source exit yields the whole-program output-halt theorem.

**Alternatives rejected.** A source evaluator defined by executing compiled
code would make refinement circular. Treating a branch, repeat or controller as
one primitive would hide instruction work. Supplying adequate fuel as a premise
would leave the query budget unproved. Requiring stopped executions to reach
segment boundaries would exclude valid early halts/faults. Each is avoided by
the actual transition-segment construction.

**Static-width choice.** The source-field predicate includes full action and
exit encodings plus branch/jump tags and both child arms. Omitting tags would
incorrectly accept small word widths, even when registers and PCs fit. The
`base+size` bound addresses resolved control targets and repeated-copy offsets.
Runtime registers, arithmetic intermediates, data addresses and machine safety
remain separate obligations with the lead's concrete query construction.

**Consequences and evidence.** Every fixed source block has a memory-independent
compiled-size instruction upper budget, exact result/read refinement and static
code fit under the displayed premises. Actual execution can use fewer steps
because unused arms and early termination are skipped. The primitive semantics,
source semantics and emitted code are unchanged. Evidence is
`compile_realizes`, `compile_correct`, `compile_run`, `compile_with_halt`,
`compile_fits`, their full expected-type consumers and the edge-case theorems
at the verified compiler source identity above.

No ADD/process rule or validation runner is introduced by this leaf; no
workflow-ledger amendment is proposed. The lead is to append the design entry
as part of coordinated integration, rather than this worker editing shared
ledgers concurrently.

## Proof digestion and live assumptions

Conceptually, the source language now has a verified connection to the physical
machine. Its compositional evaluator describes values and reads; its compiler
expands control structure into actual primitive instructions; the theorem
connects both through exact transition segments and derives an adequate fixed
budget from syntax.

In plain English, the compiler preserves what the program computes and reads,
even when a branch changes its own condition register, a load fails, or a block
halts early. Every instruction that actually runs is counted. Unused code is
still checked for representable encoded fields but contributes no executed
steps.

The live assumptions are the unchanged Lean/Std primitive and source
definitions, exact hosting/initial-PC premises for embedded blocks, and the
explicit field-fit/control-bound premises for static width. No success/readiness
or result/budget premise is hidden in compilation correctness. Natural register
semantics alone do not prove finite-width runtime safety. A caller's choice of
source must still be fixed independently of the RMQ input/query when uniformity
is claimed, and its code/scratch allocation must be counted by the final model.

A skeptical graduate student should inspect the concrete query source next:
does that fixed source implement all RMQ routes, does its scalar arithmetic stay
within the chosen word width, and does it execute against the same counted
allocation? This leaf supplies the generic compilation and instruction-budget
bridge needed by those downstream proofs; it does not replace them.
