Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

This declaration concerns the bounded PQ1-SA scalar-decoder-to-assembly leaf.
The complete packed-query capstone remains the lead's separate join.

Worker: PQ1-SA (`numeric_span`, returning). Branch:
`codex/fully-charged-packed-query-v1`. Worktree:
`C:/Users/poin/.codex/worktrees/a84a/RMQ`.
Base: `9e2720b991e203d22a2787abf66dbfb9888088fb`.
Governance: `4639223bc8130b0ef752270b5cbdd74325abcd60`.
No staging, commits, original-checkout edits, shared-ledger edits, or changes to
Primitive/Structured/Span/Compiler were performed by this worker.

Canonical `rmq-proof-sprint` preflight passed with actual runtime catalog
`rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`. The canonical skill and
completion gate remain those read for the preceding span leaf. Five explicit
requirements and seven assigned inherited invariants were frozen verbatim in
`PQ1_SPAN_ASSEMBLY_MATRIX.md` before editing.

Owned changed files are `RMQ/Core/WordRAM/Packed/SpanAssembly.lean`, this report,
and `docs/internal/packed_query/PQ1_SPAN_ASSEMBLY_MATRIX.md`.

## Fixed construction

All declarations use namespace `RMQ.SuccinctFinal.PackedWordRAM` and import
`RMQ.Core.WordRAM.Packed.SpanAssembly`.

`spanBlock base` is a fixed scalar `Structured.Block`. It uses no repetition,
runtime code generation, shape, input list, semantic reply, or proof field.
Its literal primitive expansion has 22 instruction positions; `spanRoutine`
appends one halt, `spanProgram` compiles that routine at PC zero, and `spanRun`
executes that exact program with fuel 23.

| Register | Meaning |
| --- | --- |
| base | Physical width, preserved |
| base+1 | Bit position, preserved |
| base+2 | Span length, preserved |
| base+3 | First raw reply, then shifted low fragment, then output |
| base+4 | Constant 1 |
| base+5 | First physical address, then second address on crossing |
| base+6 | Position modulo width |
| base+7 | Offset plus length |
| base+8 | Containment comparison |
| base+9 | Power-of-two mask divisor |
| base+10 | Second raw reply |
| base+11 | Low-fragment bit count |
| base+12 | High-fragment bit count |
| base+13 | Masked, then shifted high fragment |

The only scalar constant actions load 0 or 1. `spanBlock_compilation` proves the
complete literal instruction inventory, including both dormant branch arms.
At a code origin `pc`, branch/jump targets are `pc+21`, `pc+12`, `pc+20`, and
`pc+22`. The terminal wrapper's last instruction is `halt (base+3)`.

Zero length writes output zero and performs no load. A nonzero span computes
address and offset, loads the first word, and shifts it down. The contained arm
masks by `2^len`. The crossing arm increments the address, loads the second
word, masks its high fragment before shifting, then adds it to the low
fragment. Missing loads fault through the existing primitive semantics.

The source theorem is honest mathematical Nat evaluation. It in fact holds
for all numeric geometry, which includes the assigned positive-width,
len≤width domain. This does not assert `Instruction.Safe` for arbitrary Nat
inputs. The live canonical safety domain uses `len < wordWidth`; full-width
mask examples establish scalar execution, not a width-safe canonical run.

## Exact checked propositions and consumption

`spanBlock_source` takes arbitrary `base width position len memory regs` with
only `regs base=width`, `regs(base+1)=position`, `regs(base+2)=len`. For
`actual = (spanBlock base).eval memory ⟨regs,.running⟩`, it proves:

```text
SpanOutcome base (decodeSpanNat width position len memory) actual.final
and actual.reads = spanAttemptReceipts width position len memory.
```

`SpanOutcome` is expanded, not opaque evidence: if the decoder returns some
value, the actual status is running and actual register base+3 equals that
value; if it returns none, the actual status is fault. The separate
`spanBlock_source_some` and `spanBlock_source_none` theorems project those
exact alternatives.

`spanAttemptReceipts` uses this numeric memory directly. It is empty for zero
length. Otherwise it records the first attempted reply. A missing first reply
terminates the list; after a successful first reply it appends the second
attempt exactly when the span crosses. `spanAttemptReceipts_length_le` proves
length≤2. `spanAttemptReceipts_backing` retains an occurrence index and proves
the receipt at that index satisfies `receipt.reply = memory[receipt.address]?`.

`spanBlock_frame` proves for every register `r` with
`r < base+3 ∨ base+14 ≤ r` that actual source evaluation preserves `regs r`.
This includes the three inputs and covers faults. `spanBlock_static_fields`
proves for every instruction in the literal compiled body:

```text
every encoded operand/tag ≤ base + pc + 22;
every register identifier satisfies base ≤ register < base + 14.
```

`spanProgram_static_fields` gives the corresponding terminal-program bounds
with `base+23`. `spanBlock_size`, `spanRoutine_size`, and `spanProgram_length`
prove exact sizes 22, 23, and 23 respectively. These cover static fields; they
are not used as a substitute for runtime register/address-width proofs.

The generic compiler is actually consumed twice:

1. `spanBlock_machine` consumes `Structured.Block.compile_correct`. Given
   the three input equalities and `HostedAt program codeStart
   ((spanBlock base).compileAt codeStart)`, it derives `used≤22` such that the
   literal `run memory program used ⟨regs,codeStart,.running⟩` has the exact
   decoder output/status, exact ordered attempts, the same final register
   frame, `steps=used`, and continuation PC `codeStart+22` when running.
2. `spanRun_correct` consumes `Structured.Block.compile_run` on the exact
   `spanRoutine base`. For the same input-register equalities it proves:

```lean
(spanRun base memory regs).result = decodeSpanNat width position len memory ∧
(spanRun base memory regs).final.status =
  (match decodeSpanNat width position len memory with
  | none => .fault
  | some value => .halted value) ∧
(spanRun base memory regs).reads = spanAttemptReceipts width position len memory ∧
(∀ r, r < base + 3 ∨ base + 14 ≤ r →
  (spanRun base memory regs).final.regs r = regs r) ∧
(spanRun base memory regs).steps ≤ 23
```

`spanRun_inputs` initializes only the three scalar inputs and discharges all
those equalities, yielding the decoder-result equality, exact receipts, and
23-step budget with no semantic premises. Adequacy comes from the compiler
proof; fuel 23 is the proven syntax-derived program size.

`spanRun_prefix_frame` additionally proves that every register outside
`[base,base+14)` is unchanged at every primitive prefix of the same program,
for arbitrary prefix fuel. Its proof uses the literal instruction register
inventory and actual instruction execution, not final-state restoration.

`spanRun_steps_partition` proves that this same run's steps equal the sum of
its memory-read, register-write, arithmetic, comparison, branch, and control
category counts. `spanRun_read_at` retains transition index, actual prefix
pre-state, fetched instruction, execution equation, load address-register
value, and exact same-memory reply. Failed loads are included.

## Boundary checks and anti-vacuity

The six compiled consumers reduce actual `spanRun` projections in the kernel.
They pin explicit expected values, exact ordered receipts, and actual steps:

| Case | Result/status | Receipts | Steps |
| --- | --- | --- | --- |
| Zero length, empty physical memory | some 0 | [] | 3 |
| Contained span, width4 position1 length2, memory[13] | some 2 | [(0,some13)] | 14 |
| Crossing span, width4 position3 length3, memory[13,3] | some 7 | [(0,some13),(1,some3)] | 19 |
| Missing first word for crossing span | fault | [(0,none)] | 5 |
| Missing second word for crossing span, memory[13] | fault | [(0,some13),(1,none)] | 11 |
| All-ones raw word, width4 position0 length4, memory[15] | some 15 | [(0,some15)] | 14 |

`SpanCompiledExamples.returnedValue_dependency` proves that changing the
crossing first word from13 to5 or the second word from3 to2 changes the actual
returned option. This constrains the value projection itself. It does not
infer sensitivity to irrelevant bits. Failure receipts constrain the same
run's ordered list, so a phantom second attempt after first failure would
contradict the checked missing-first consumer. The arbitrary-memory universal
theorems supplement these finite boundaries. No source-mutation campaign is
claimed; all fixtures are versioned in the owned Lean file.

## Verification and ownership

Final source SHA256:
`0c6b9ab9c5d5d2338b413ba8d55683302b1de7a667de193f7e294fafc8bd0f60`.

Final check used Lean4.22.0 and only the independent local cache:

```powershell
$env:LEAN_PATH = (Join-Path (Get-Location) '.lake/build/lib/lean')
& C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe `
  -o .lake/build/lib/lean/RMQ/Core/WordRAM/Packed/SpanAssembly.olean `
  -i .lake/build/lib/lean/RMQ/Core/WordRAM/Packed/SpanAssembly.ilean `
  RMQ/Core/WordRAM/Packed/SpanAssembly.lean
```

Result: exit0, no warnings, 5.71 seconds. Both artifacts are available. An
earlier full source/machine check passed in9.23 seconds; later prefix-frame,
static-wrapper and exact-step fixture additions were checked in7.89 seconds,
then the final check removed one unused simp argument. Development failures
were ordinary local proof elaboration issues (shift lemma syntactic heads,
attempt-list match splitting, quantified field-case splitting, a lambda's
write namespace, and a missing local expected type); captured tool output
identified each surface and each retry followed a source repair. No command
timed out and no unchanged expensive invocation was repeated.

Build-slot transfers were coordinated with the lead, compiler, and metadata
workers. Two early handoff messages crossed because both recipients understood
the same root release as theirs; subsequent transfers required explicit
sender-to-recipient release. Final source and artifact checks occurred in that
explicit exclusive slot. The slot was released immediately afterward.

Owned-file trust/native-decision hygiene and working/new-file whitespace checks
pass. Strict UTF-8 byte comparison passes for all five frozen prompt blocks
and seven inherited invariant blocks, with no missing, duplicate or changed
IDs. The full evidence matrix is `PQ1_SPAN_ASSEMBLY_MATRIX.md`.

The lead explicitly owns strict design-policy validation at the governing
base, committed-range whitespace after integration, and all broad/public
capstone checks. They are not claimed here. No workflow mechanism was changed.

## Proposed design-ledger detail

Suggested addition under the existing PQ1 physical-machine/repacking decision:

The numeric span adapter now has a fixed scalar source and a checked primitive
compilation. Its22-position body uses fourteen register slots, with preserved
inputs and ten scratch slots; one appended halt gives a syntax-derived budget
of23 primitive instructions. A separate attempted-receipt definition models
short-circuit failure, and both source evaluation and primitive execution are
proved equal to it. The rejected alternative was treating the geometric
two-cell plan as an executed failure trace, which would invent a second read
after a missing first word. Static instruction/register bounds include dormant
arms and code targets, while the canonical per-state width proof remains
separate. Evidence: `spanBlock_compilation`, `spanBlock_machine`,
`spanRun_correct`, `spanRun_prefix_frame`, and the compiled boundary consumers.

## Proof digestion

Conceptually, the bridge now connects three descriptions of one computation:
numeric bit-span decoding, a fixed scalar source program, and actual primitive
instruction execution. The source proof follows explicit scalar operations;
the generic compiler transports that result and the exact read list to the
machine without supplying a desired answer or an adequacy premise.

In plain English, the decoder is executable as a small fixed routine. It
computes its answer from the words it really reads, stops faithfully on missing
memory, and changes no register outside its assigned area along the way.

Live source assumptions are only the register-input equalities; initialized
machine consumers discharge them. The primitive model uses Nat
representatives. Canonical machine safety additionally needs positive width,
strictly shorter spans for mask powers, bounded physical words and arithmetic
results, and representable addresses. Those per-state width and whole-query
composition obligations are expressly lead-owned, not asserted by this leaf.

A skeptical reader should compare the literal instruction list with the source
routine, inspect how the missing-first branch avoids the second attempt, and
follow the compiler consumer to the exact `spanRun` projections. The next
assigned consumer can use `spanBlock_machine` as an embedded segment or
`spanRun_correct` as a standalone scalar routine.
