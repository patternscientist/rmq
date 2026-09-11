Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

This declaration covers only the PQ1-QS generic source-safety to actual
compiled-safety leaf. The canonical full-query source-safety proof and the
complete packed-query capstone remain lead-owned targets.

## Identity and scope

- Worker: PQ1-QS, returning `primitive_calculus` subagent.
- Worktree: `C:/Users/poin/.codex/worktrees/a84a/RMQ`.
- Branch: `codex/fully-charged-packed-query-v1`.
- Assigned exact base: `9e2720b991e203d22a2787abf66dbfb9888088fb`.
- Governance: `4639223bc8130b0ef752270b5cbdd74325abcd60`.
- Actual runtime skills: `rmq-audit-prompt`, `rmq-coordinator`,
  `rmq-proof-sprint`. Canonical proof-sprint skill/completion gate applied;
  required project-skill preflight passed at entry.
- Lead's parallel integration advanced HEAD to
  `b0af10d14121c7b11a7d3eb7cb1515c618a0da4b`; this worker did not change the
  branch, stage files, commit, or edit any shared/interface file.
- Owned delivery: `RMQ/Core/WordRAM/Packed/Safety.lean`,
  `PQ1_SAFETY_MATRIX.md`, and this report. Source integration is pending.
- Final Safety source SHA256:
  `8325aa084412c85f81b9e7ec0868679cfbbd7086fc9eb3f61015d4c46cadd9aa`.

The [completed matrix](PQ1_SAFETY_MATRIX.md) preserves all ten assigned
requirements and inherited rows. The same width, memory, source data, program,
initial state and actual run are retained across the proof chain.

Unchanged imported source hashes:

| File | SHA256 |
| --- | --- |
| Primitive | `5aff5c4e88267794cd3582a821d82a033d8364650ca1e353d7fd590877b52bf6` |
| Calculus | `61c1bb9f5c14f4f40fb3f1f13d2d3a35967b8a90a3fa97639cd8d54ba0ac9f53` |
| Structured | `5cde17b16464526272a4cac619a83cf7015d6d5db2725839ca26cf6f9d48198c` |
| Compiler | `0c527f0cd9db8be2860bcf1815826bbeed05e22d3660e450285f70dddfaeff60` |

## Exact source-safety semantics

All names below are in `RMQ.SuccinctFinal.PackedWordRAM.Structured`; primitive
types resolve to the existing parent namespace. These are proof predicates,
not executable machine inputs or source-evaluator callbacks.

```lean
def Data.Fits (width : Nat) (s : Data) : Prop :=
  (∀ r, s.regs r < 2 ^ width) ∧
  (∀ value, s.status = .halted value → value < 2 ^ width)

def Action.LocalSafe (memory : Memory) (width : Nat) (op : Action) (s : Data) : Prop :=
  match op with
  | .load _ address => ∀ value, memory[s.regs address]? = some value → value < 2 ^ width
  | .constant _ value => value < 2 ^ width
  | .move _ src => s.regs src < 2 ^ width
  | .arithmetic op _ lhs rhs =>
      op.eval (s.regs lhs) (s.regs rhs) < 2 ^ width ∧
      (op = .sub → s.regs rhs ≤ s.regs lhs) ∧
      (op = .div ∨ op = .mod → 0 < s.regs rhs) ∧
      (op = .shl ∨ op = .shr → s.regs rhs < width)
  | .comparison op _ lhs rhs => op.eval (s.regs lhs) (s.regs rhs) < 2 ^ width

def IterationsSafe (safe : Data → Prop) (body : Data → Evaluation) : Nat → Data → Prop
  | 0, _ => True
  | count + 1, s => safe s ∧ IterationsSafe safe body count (body s).final

def Block.Safe (memory : Memory) (width : Nat) (block : Block) (s : Data) : Prop :=
  s.Fits width ∧ (s.status = .running →
    match block with
    | .skip => True
    | .action op => op.LocalSafe memory width s
    | .exit src => s.regs src < 2 ^ width
    | .seq first second => first.Safe memory width s ∧
        second.Safe memory width (first.eval memory s).final
    | .ifZero condition zero nonzero =>
        if s.regs condition = 0 then zero.Safe memory width s else nonzero.Safe memory width s
    | .repeat count body => IterationsSafe (body.Safe memory width) (body.eval memory) count s)
```

The `True` cases correspond exactly to no scalar operation (`skip` or zero
iterations); entry data must still fit. Every live arithmetic operation has
the displayed concrete safeguards. Missing loads impose no invented returned
word, but their address is constrained by fitting registers and the actual
execution retains its failed receipt and fault status.

Usable constructor rules are `Block.safe_stopped`, `safe_skip`, `safe_action`,
`safe_exit`, `safe_seq`, `safe_ifZero`, and `safe_repeat`.
`IterationsSafe.zero/succ` construct finite iteration obligations;
`IterationsSafe.of_invariant` discharges them from a preserved source invariant.
`IterationsSafe.at` proves:

```lean
IterationsSafe safe body count s →
  ∀ index, index < count → safe (iterate body index s).final
```

Local operational preservation is checked independently of the compiler:

```lean
theorem Action.eval_fits (memory : Memory) (width : Nat) (op : Action) (s : Data)
    (fit : s.Fits width) (safe : op.LocalSafe memory width s) :
    (op.eval memory s).final.Fits width

theorem Block.eval_fits (memory : Memory) (width : Nat) (block : Block) (s : Data)
    (safe : block.Safe memory width s) : (block.eval memory s).final.Fits width

theorem Action.execute_safe (memory : Memory) (width : Nat) (op : Action) (s : State)
    (fit : s.Fits width) (fields : op.instruction.Fits width)
    (safe : op.LocalSafe memory width (Data.ofState s)) (pc : s.pc + 1 < 2 ^ width) :
    Instruction.Safe width s op.instruction ∧ (execute memory op.instruction s).1.Fits width
```

All arithmetic safeguards are projected into the unchanged primitive
`Instruction.Safe`; the result bound also proves the written register fits.
Load-reply bounds are used to prove the actual post-state fits. No oversized
result is truncated and no primitive semantics is changed.

## Exact compiled execution and prefix claims

`SafeRealizes` strengthens the existing exact transition-segment proof with
final-state fit and `TraceSafe`. The latter asserts primitive instruction
safety and post-state fit for every transition in the actual segment. The
public result retains explicit occurrence indices:

```lean
theorem Block.compile_safe_correct (memory : Memory) (program : Program) (width : Nat)
    (block : Block) (base : Nat) (s : State) (hpc : s.pc = base)
    (host : HostedAt program base (block.compileAt base))
    (fields : block.FieldsFit width) (bound : base + block.size < 2 ^ width)
    (fit : s.Fits width) (safe : block.Safe memory width (Data.ofState s)) :
    ∃ used, used ≤ block.size ∧
      Data.ofState (run memory program used s).final =
        (block.eval memory (Data.ofState s)).final ∧
      (run memory program used s).reads = (block.eval memory (Data.ofState s)).reads ∧
      (run memory program used s).steps = used ∧
      ((run memory program used s).final.status = .running →
        (run memory program used s).final.pc = base + block.size) ∧
      (run memory program used s).final.Fits width ∧
      (∀ (index : Nat) (t : Transition), (run memory program used s).transitions[index]? = some t →
        Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
      (∀ index, index ≤ used → (run memory program index s).final.Fits width)
```

The proof is structural over the unchanged source/compiler. Scalar actions
consume `Action.execute_safe`. Control steps bound branch, jump and fallthrough
PCs. Sequence and fixed repetition use the actual source-evaluated successor
data; halted/faulted segments terminate without entering later code. The
nonzero branch's final jump executes only when its arm remains running.

`run_prefix_fits` is proved by actual `step`/`run` induction. It includes prefix
zero, the final prefix, and saturated prefixes after early termination. The
standalone consumer exposes the full fixed-size budget directly:

```lean
theorem Block.compile_run_safe (memory : Memory) (width : Nat) (block : Block)
    (s : State) (hpc : s.pc = 0) (fields : block.FieldsFit width)
    (bound : block.size < 2 ^ width) (fit : s.Fits width)
    (safe : block.Safe memory width (Data.ofState s)) :
    Data.ofState (run memory (block.compileAt 0) block.size s).final =
      (block.eval memory (Data.ofState s)).final ∧
    (run memory (block.compileAt 0) block.size s).reads =
      (block.eval memory (Data.ofState s)).reads ∧
    (run memory (block.compileAt 0) block.size s).steps ≤ block.size ∧
    ((run memory (block.compileAt 0) block.size s).final.status = .running →
      (run memory (block.compileAt 0) block.size s).final.pc = block.size) ∧
    (run memory (block.compileAt 0) block.size s).final.Fits width ∧
    (∀ (index : Nat) (t : Transition), (run memory (block.compileAt 0) block.size s).transitions[index]? = some t →
      Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
    (∀ index, index ≤ block.size →
      (run memory (block.compileAt 0) index s).final.Fits width)
```

For the appended-halt theorem, let `source := block.eval memory (Data.ofState s)`,
`program := block.compileAt 0 ++ [.halt output]`, and
`actual := run memory program (block.size+1) s`.
`Block.compile_with_halt_safe` assumes the same source safety/initial fit/PC and
field-fit premises, plus `(Instruction.halt output).Fits width` and
`block.size+1 < 2^width`. Its exact conclusion is:

```lean
Data.ofState actual.final = ((Block.exit output).eval memory source.final).final ∧
actual.result = (match source.final.status with
  | .running => some (source.final.regs output)
  | .halted value => some value
  | .fault => none) ∧
actual.reads = source.reads ∧ actual.steps ≤ program.length ∧
actual.final.Fits width ∧
(∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
  Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
(∀ index, index ≤ block.size + 1 → (run memory program index s).final.Fits width)
```

This is the identical program, memory, initial state, result and receipt object
as `Compiler.compile_with_halt`, with runtime safety added. It does not conjoin
safety for a sibling execution. Dormant encoded fields remain covered by
`FieldsFit` and the unchanged `compile_fits` theorem at this same width.

The read-width projection retains actual occurrence and backing:

```lean
theorem run_read_fits {memory : Memory} {program : Program} {fuel width : Nat}
    {s : State} {index : Nat} {t : Transition} {receipt : Receipt}
    (occurrence : (run memory program fuel s).transitions[index]? = some t)
    (read : t.receipt = some receipt)
    (safe : Instruction.Safe width t.before t.instruction) (afterFit : t.after.Fits width) :
    receipt.address < 2 ^ width ∧ receipt.reply = memory[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ width)
```

Its proof consumes `run_read_at`: the same index yields the actual load
instruction, pre-state, address-register value and memory reply. Before-state
fit bounds even failed addresses; successful execution writes the returned word
to the destination, whose post-state bound proves reply fit.

## Consumers and non-vacuity

`SafetyConsumers.hosted_expectedType`, `standalone_expectedType`, and
`halt_expectedType` spell and consume the complete expected public types,
including result/read/budget, instruction-occurrence and prefix conclusions.
The expected types are not inferred from their referenced theorem declarations.

`arithmetic_source_safe` is symbolic in width, arithmetic opcode and two operand
values. It accepts explicit operand/result fit and all sub/divisor/shift guards.
`arithmetic_compiled_safe` consumes that source proof plus code/halt-field and
PC bounds to prove the actual two-instruction arithmetic/halt run's result,
every instruction's safety and every prefix's fit.

| Kernel consumer | Exact boundary |
| --- | --- |
| `legal_boundary` | At width 4, actual add/halt on operands 14 and 1 returns 15; both instruction occurrences and all prefixes 0 through 2 are safe/fitting. |
| `underflow_rejected` | Negates the exact `Block.Safe` predicate for subtraction `0-1`, even though saturating Nat subtraction would return fitting zero. |
| `zero_divisor_rejected` | Negates `Block.Safe` for division `8/0`. |
| `zero_modulus_rejected` | Negates `Block.Safe` for modulus `8%0`. |
| `excessive_right_shift_rejected` | Negates `Block.Safe` for shift amount 4 at width 4, despite a fitting result. |
| `excessive_left_shift_rejected` | Negates `Block.Safe` for shifting zero by 4 at width 4; the shift guard itself fails. |
| `overflowing_result_rejected` | Negates `Block.Safe` for `15+1` at width 4; both input operands fit and the result reaches the excluded capacity 16. |
| `failed_address_rejected` | Negates `Block.Safe` with load address 16 at width 4 even though memory is empty and the attempted reply would be absent. |
| `missing_load_safe` | Actual load/halt at the largest representable address 15, width 4 and empty memory, returns no result, records `(15,none)`, uses one step and keeps every prefix through budget 2 fitting. |

These negations target the same accepted `Block.Safe`, at explicit source
states/widths. They are not stronger proxy predicates or differences caused
only by a log field. `operandData_fits` separately proves the legal operand-data
bounds used by the symbolic and concrete tests. The final code contains the
replayable kernel propositions themselves; no mutation campaign is claimed.

## Verification

Final narrow command:

```powershell
$env:LEAN_PATH = Join-Path $PWD '.lake/build/lib/lean'
& 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe' `
  -o .lake/build/lib/lean/RMQ/Core/WordRAM/Packed/Safety.olean `
  -i .lake/build/lib/lean/RMQ/Core/WordRAM/Packed/Safety.ilean `
  RMQ/Core/WordRAM/Packed/Safety.lean
```

| Check | Outcome |
| --- | --- |
| Canonical project-skill preflight | PASS at assigned entry base with actual runtime catalog. |
| Local source/action safety and source preservation | Exit 0, no warnings, 1.95s. |
| Complete safe compiler segment and generic prefix induction | Exit 0, no warnings, 1.77s. |
| Public hosted/standalone/appended-halt safe-run corollaries | Exit 0, no warnings, 4.09s. |
| Final module, exact-type/symbolic/negative/read-width consumers, `.olean`/`.ilean` emission | Exit 0, no warnings, 5.52s; command chunk `3a37d5`; final source SHA256 above. |
| Trust/import and native-decision scans | No forbidden-token, Mathlib, `native_decide` or `Lean.ofReduceBool` matches in `Safety.lean`. |
| Interface hashes | All four imported source identities match their earlier verified versions. |
| Owned whitespace checks | No defects under scoped `git diff --check` and no-index checks for new files; only normal LF-to-CRLF notices. No-index exit 1 indicates a new file differs from `/dev/null`. |
| Frozen requirement preservation | All ten exact requirement columns retained during evidence updates and checked against prompt/gate text. |

Short development failures were local elaboration issues: projecting a
structurally recursive predicate before exposing its constructor, eliminating
empty-list membership, explicit transition binder annotations, and a parameter
named with a reserved token. Each was repaired before the subsequent narrow
check. No timeout, unchanged expensive retry, aggregate build or external
runtime callback occurred. Build-slot handoffs were coordinated with the lead
and other workers; no Safety process remains.

Broad gates are intentionally lead-owned for this bounded additive leaf,
including strict design checking at the exact governance base and the
committed-range whitespace check after integration. A final public-capstone
blind exact-commit audit is not replaced by this local verification.

## Proposed design entry for lead append

**Title:** Preserve explicit source word safety through actual primitive compilation.

**Context.** Static code-field fit does not constrain runtime register values,
load replies, divisors, shifts or arithmetic results. The fully charged query
needs those local facts carried into the same execution that computes its
answer and emits its receipts, including faults and early exits.

**Decision.** Define `Data.Fits`, constructor-local `Action.LocalSafe`, and
`Block.Safe` over the independent source evaluator. Source sequence and branch
rules use actual evaluated data; `IterationsSafe` checks every finite source
iteration and has an invariant-based introduction rule. Scalar preservation
proves both source-data fit and the unchanged primitive `Instruction.Safe` plus
post-state fit. Strengthen exact compiler segments with these actual-transition
properties, then derive occurrence-indexed instruction safety and every prefix's
`State.Fits` by primitive execution induction.

**Alternatives rejected.** Defining source safety as compiled safety would
assume the desired result. Looking only at instruction operands would miss
loaded/produced values and failed addresses. Truncating Nat arithmetic or
changing width per query would change the model. Checking only a final state
would miss overflowing intermediates. Requiring stopped code to reach the
normal end PC would discard valid fault/early-halt executions. The chosen proof
handles each directly without changing ISA, evaluator or compiler.

**Consequences.** Hosted segments have existentially produced exact fuel, since
running longer inside an arbitrary hosting program could enter its successor.
Standalone code and appended halt have fixed syntax-derived adequate fuel and
safety for all prefixes through that budget. Failed loads retain their receipt;
their addresses still fit. Dormant encoded fields use the existing separate
static code theorem. Full allocated-memory word bounds, concrete source safety,
global width scaling and the canonical query remain separate proof obligations
for the lead, explicitly outside this generic leaf.

**Evidence.** `Action.execute_safe`, `Block.eval_fits`,
`compile_safe_realizes`, `compile_safe_correct`, `compile_run_safe`,
`compile_with_halt_safe`, `run_read_fits`, and their full expected-type and
same-predicate boundary consumers at the verified Safety source identity above.
Focused private analogues of compiler composition/PC helpers were proved
locally because those helpers are private; no shared-interface change was
needed. No ADD/process decision or workflow-ledger amendment is introduced.

## Proof digestion and next canonical obligation

Conceptually, local arithmetic and memory facts now travel with the actual
compiled execution. The proof no longer stops at representable code fields:
it checks the values before and after each executed instruction and connects
those states to every execution prefix.

In plain English, a proved safe source routine produces a machine run whose
register values, control addresses and successful read words fit one declared
width. It cannot silently divide by zero, underflow a subtraction, shift too far
or overflow a result. A missing load may fault safely and still counts its
attempted read.

The live hypotheses are the exact source `Block.Safe`, same-width static field
fit, initial state fit/PC and strict compiled endpoint bound displayed above.
They contain no compiled-run safety, desired result or adequate-fuel assumption.
The source judgment itself remains to be proved for the lead's concrete full
query. This generic theorem bounds accessed numeric words; full allocation-wide
cell-width and succinct-space claims belong to the canonical builder proof.

A skeptical graduate student should inspect the next concrete `Block.Safe`
proofs: are the actual span/metadata/query intermediates bounded, do they use
the same allocation and width, and are all rare/failed routes included? Those
canonical proofs can now invoke these checked compiler and prefix interfaces.
