Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

Frozen completed evidence matrix: [PQ1_LOAD_SAFETY_MATRIX.md](PQ1_LOAD_SAFETY_MATRIX.md).

## Scope and identity

Assigned base: `b0af10d14121c7b11a7d3eb7cb1515c618a0da4b`. Governance: `4639223bc8130b0ef752270b5cbdd74325abcd60`. The canonical proof-sprint preflight passed at the assigned base with runtime catalog `rmq-coordinator,rmq-proof-sprint,rmq-audit-prompt`. Root advanced the shared construction checkpoint to `067b6ffd350aee08f1496335ce957895f0da3fcc` during this leaf.

Only `RMQ/Core/WordRAM/Packed/LoadSafety.lean`, the LW matrix, and this report were edited. No staging, commits, branch/worktree changes, existing module edits, or shared-ledger changes. All four worker slots were already occupied with independent useful work, so this bounded leaf stayed local.

## Exact assumptions and numeric meaning

`MemoryWordsFit memory width` is exactly `∀ value ∈ memory, value < 2 ^ width`. It contains no successful-read/presence assumption. `Data.Fits width s` bounds every register and every existing halted result. A running span has width, position, and length in the three actual input registers; width is at least 2, position is below capacity, and length is strictly below width. Stopped data are covered with the same entry-fit premise. Source setup requires width at least 8; its only arithmetic values are actual constants 0 through 173 and raw successful replies.

Source scalar safety and code-field safety remain separate. A width-2 span source can be safe even though its entire 23-position terminal program cannot fit that code width. Actual standalone span safety uses `base + 23 < 2^width`. Generic hosted consumers permit explicit static/end-PC premises. Canonical consumers discharge these premises using the one query-independent `wordWidth xs.length`, including register banks 8192 and 8256.

## Checked propositions

```lean
theorem span_offset_sum_fit (width offset len : Nat) (hw : 2 ≤ width)
    (ho : offset < width) (hl : len < width) : offset + len < 2 ^ width
```

```lean
theorem span_next_address_fit (width position : Nat) (hw : 2 ≤ width)
    (hp : position < 2 ^ width) : position / width + 1 < 2 ^ width
```

```lean
theorem span_crossing_bounds (width offset len first second : Nat)
    (ho : offset < width) (hl : len < width) (cross : width < offset + len)
    (hf : first < 2 ^ width) :
    0 < offset ∧ 0 < width - offset ∧ width - offset < width ∧
    width - offset ≤ len ∧ len - (width - offset) < width ∧
    first / 2 ^ offset < 2 ^ (width - offset) ∧
    second % 2 ^ (len - (width - offset)) * 2 ^ (width - offset) < 2 ^ len ∧
    first / 2 ^ offset +
      second % 2 ^ (len - (width - offset)) * 2 ^ (width - offset) < 2 ^ len
```

```lean
theorem spanBlock_safe (base width position len : Nat) (memory : Memory)
    (s : Data) (hw : 2 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (fit : s.Fits width) (hwreg : s.regs base = width)
    (hpreg : s.regs (base + 1) = position) (hlreg : s.regs (base + 2) = len)
    (hp : position < 2 ^ width) (hl : len < width) :
    (spanBlock base).Safe memory width s
```

```lean
theorem metadataSetupFrom_safe (memory : Memory) (width start count : Nat)
    (memoryFit : MemoryWordsFit memory width) (bound : start + count ≤ 2 ^ width)
    (s : Data) (fit : s.Fits width) :
    (metadataSetupFrom start count).Safe memory width s
```

```lean
theorem metadataSetupBlock_safe (memory : Memory) (width : Nat)
    (hw : 8 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (s : Data) (fit : s.Fits width) : metadataSetupBlock.Safe memory width s
```

```lean
theorem buildMemory_setup_safe (xs : List Int) (s : Data)
    (fit : s.Fits (wordWidth xs.length)) :
    metadataSetupBlock.Safe (buildMemory xs) (wordWidth xs.length) s
```

```lean
theorem spanBlock_fieldsFit (base width : Nat) (bound : base + 23 < 2 ^ width) :
    (spanBlock base).FieldsFit width
```

```lean
theorem spanBlock_machine_safe (base codeStart width position len : Nat)
    (memory : Memory) (program : Program) (regs : Registers)
    (hw : 2 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (registerFit : ∀ r, regs r < 2 ^ width)
    (hwreg : regs base = width) (hpreg : regs (base + 1) = position)
    (hlreg : regs (base + 2) = len) (hp : position < 2 ^ width) (hl : len < width)
    (host : HostedAt program codeStart ((spanBlock base).compileAt codeStart))
    (fields : (spanBlock base).FieldsFit width) (endFit : codeStart + 22 < 2 ^ width) :
    ∃ used, used ≤ 22 ∧
      let actual
```

```lean
theorem spanRun_safe (base width position len : Nat) (memory : Memory)
    (regs : Registers) (hw : 2 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (registerFit : ∀ r, regs r < 2 ^ width)
    (hwreg : regs base = width) (hpreg : regs (base + 1) = position)
    (hlreg : regs (base + 2) = len) (hp : position < 2 ^ width) (hl : len < width)
    (codeFit : base + 23 < 2 ^ width) :
    let actual
```

```lean
theorem spanRun_canonical_safe (xs : List Int) (base position len : Nat)
    (baseFit : base + 23 < 2 ^ 32) (hp : position < 2 ^ wordWidth xs.length)
    (hl : len < wordWidth xs.length) :
    let width
```

```lean
theorem buildMemory_setup_run_safe (xs : List Int) (s : State)
    (hpc : s.pc = 0) (hs : s.status = .running)
    (registerFit : ∀ r, s.regs r < 2 ^ wordWidth xs.length) :
    let width
```

```lean
theorem metadataSetupBlock_hosted_safe (memory : Memory) (program : Program)
    (width base : Nat) (s : State) (hw : 8 ≤ width)
    (memoryFit : MemoryWordsFit memory width) (fit : s.Fits width)
    (hpc : s.pc = base) (host : HostedAt program base (metadataSetupBlock.compileAt base))
    (fields : metadataSetupBlock.FieldsFit width) (endFit : base + 348 < 2 ^ width) :
    ∃ used, used ≤ 348 ∧
      Data.ofState (run memory program used s).final =
        (metadataSetupBlock.eval memory (Data.ofState s)).final ∧
      (run memory program used s).reads = (metadataSetupBlock.eval memory (Data.ofState s)).reads ∧
      (run memory program used s).steps = used ∧
      ((run memory program used s).final.status = .running →
        (run memory program used s).final.pc = base + 348) ∧
      (run memory program used s).final.Fits width ∧
      (∀ (index : Nat) (t : Transition), (run memory program used s).transitions[index]? = some t →
        Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
      (∀ index, index ≤ used → (run memory program index s).final.Fits width)
```

```lean
theorem spanRun_safe_read (base width position len : Nat) (memory : Memory)
    (regs : Registers) (hw : 2 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (registerFit : ∀ r, regs r < 2 ^ width)
    (hwreg : regs base = width) (hpreg : regs (base + 1) = position)
    (hlreg : regs (base + 2) = len) (hp : position < 2 ^ width) (hl : len < width)
    (codeFit : base + 23 < 2 ^ width) (index : Nat) (t : Transition) (receipt : Receipt)
    (occurrence : (spanRun base memory regs).transitions[index]? = some t)
    (read : t.receipt = some receipt) :
    receipt.address < 2 ^ width ∧ receipt.reply = memory[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ width)
```

```lean
theorem canonical_setup_size_installed (xs : List Int) :
    let initial : State
```

```lean
theorem failed_setup :
    let width
```

```lean
theorem canonical_width_and_memory (xs : List Int) :
    MemoryWordsFit (buildMemory xs) (wordWidth xs.length) ∧
    (buildMemory xs).length < 2 ^ wordWidth xs.length ∧
    wordWidth xs.length ≤ 192 * (Nat.log2 (xs.length + 2) + 1)
```

## Same-object proof chain

1. `MemoryWordsFit.reply` uses the actual equation `memory[address]? = some value` and `List.mem_of_getElem?`. Failed replies require no fabricated value; the address is still represented by a fitting register.

2. `span_offset_sum_fit` proves the actual offset-plus-length addition fits from width 2. `span_next_address_fit` proves the quotient-plus-one value fits before any second lookup, including a failed one. `span_crossing_bounds` proves both subtraction orders, both shift ranges, a bounded first fragment, the masked second fragment, and their actual sum below `2^len`. It never concatenates two full physical words.

3. The private `localChecks` predicate inspects the actual source scalar operands and source-evaluated intermediate states. `localChecks_safe` proves by syntax induction that these checks and entry `Data.Fits` imply the public `Block.Safe`; register/result preservation uses the existing checked `Block.eval_fits`. Five separately checked span paths cover zero length, missing first reply, contained success, missing second reply, and crossing success. Their proof tactic steps through one source action and normalizes only that resulting state. Initial halted/faulted data use the stopped-source lemma.

4. `metadataSetupFrom_safe` inducts over the actual constant/load pairs. Each next source state is obtained by the preceding pair evaluator. The generic memory-fit implication covers every successful raw reply; a fault preserves the fit invariant and stops the suffix. `buildMemory_setup_safe` discharges memory and minimum-width facts with `buildMemory_words_fit` and the definition of `wordWidth`, without readiness.

5. Hosted span uses one existential `used` from `Block.compile_safe_correct`. Its source-data and ordered-read equalities transport `spanBlock_source` and the frame theorem into precisely `run memory program used initial`. The instruction and prefix clauses are retained from that same returned run, not from an independently selected fuel witness. Standalone span uses exactly `spanRun base memory regs = run memory (spanProgram base) 23 initial`; `Block.compile_run_safe` and `spanRun_correct` have these same object arguments.

6. Canonical setup uses exactly `run (buildMemory xs) (metadataSetupBlock.compileAt 0) 348 s` in both the existing installed-field/receipt theorem and the new safety compiler consumer. Each installed field equals its own actual numeric slot. The metadata-facing receipt expression is related to the executed memory by `buildMemory_metadata_prefix`; `canonical_setup_size_installed` explicitly retains receipt occurrence 0 and the installed input-size field.

7. Canonical allocation object identity is `buildMemory xs = shapeMemory (cartesianShape xs)`, whose definition is the fixed metadata followed by repacked reviewer payload at `wordWidth`. `buildMemory_words_fit`, `buildMemory_length_fit`, and `wordWidth_le_log` concern this same memory and width. The actual loader safety/value/receipt consumers also use this exact `buildMemory xs`; there is no substitute semantic table or detached counted store. Existing allocation payload accounting remains with the lead, and this leaf adds no stored words or proof-carried answers.

## Checked consumers and challenges

- `span_source_requiredFacts` independently states the full arbitrary-memory source type with the explicit universal word bound. `setup_source_requiredFacts` does the same for setup. The hosted, standalone, and canonical run consumers each state the complete safety/value/receipt/budget proposition before consuming compiler results.

- `width_two_zero` checks the admitted minimum source width and zero-read branch. `all_ones_crossing` checks actual replies 255,255 at width 8, the maximal seven-bit result 127, ordered addresses 0,1, and instruction/prefix safety. This challenges overflow-prone full-word concatenation and missing masking.

- `missing_first` and `missing_second` require actual fault status and ordered receipts containing `none`; the second fixture retains its successful first reply. `failed_setup` requires the actual first metadata load to fault on empty numeric memory and still proves every fixed-budget prefix safe. These would reject silently padded successful reads.

- `canonical_banks` instantiates the bounded-base theorem at both 8192 and 8256. The general canonical theorem retains all instruction/prefix clauses, result/status/reads/frame and budget. `canonical_setup_edges` and `canonical_setup_size_installed` cover empty and singleton input lists, including actual installed values 0 and 1 and first-receipt backing.

- `spanRun_safe_read` retains an actual transition occurrence, the raw receipt equation, representable attempted address, and successful reply bound. No set-membership replacement discards occurrence order.

No mutation campaign is claimed. The prompt did not assign one; the replay-only invariants therefore do not apply. These are checked symbolic propositions and independent expected-value/type consumers, not report-only mutation evidence.

## Verification ledger

- Preflight: PASS at the exact assigned base and governance ref.

- Development: the initial whole-path `simp` proof reached 200000 heartbeats; one exploratory increased-budget pass also timed out. The proof was replaced, without another budget increase, by single-action normalization, explicit raw-`Nat.shiftLeft`/`Nat.shiftRight` numeric lemmas, and five separately checked paths. Later diagnostics isolated tactic backtracking, generated case indentation, and unnecessary repeated context simplification. Every retry followed a source repair; no unchanged expensive command was rerun.

- Semantic final compile: direct local Lean `-o/-i LoadSafety.lean` PASS, no warnings, 10.3341274 seconds, command chunks `befd4c`/`d368e6`. Emitted `.olean` and `.ilean`.

- Imported artifact check: independently written source expected types plus five printed axiom inventories PASS, 1.7271481 seconds, chunk `b7c568`. `spanBlock_safe`, canonical span, canonical setup run and failed setup depend only on `propext`, `Classical.choice`, `Quot.sound`; generic setup source uses only `propext`, `Quot.sound`.

- Repository-wide trust scans over `RMQ` and `lakefile.toml` found no forbidden proof/runtime keywords, Mathlib imports, `native_decide`, or `Lean.ofReduceBool` (chunk `964cab`).

- Whitespace scan found one extra EOF blank line in the new source, which was removed. The source now passes `git diff --no-index --check` against `/dev/null`; only the normal LF-to-CRLF notice remains. The final identity compile/import checks below passed after that byte change.

- Final clean-byte `-o/-i` compile: PASS, no warnings, 9.3711686 seconds. Final imported exact source consumers and the same five axiom inventories: PASS, 2.1893894 seconds. Command chunks `beffad`/`072175`. Source SHA256: `26b32ef5d4c651b4862b555326a3a8c027219ed7ac2f9c7591202146861909d8`. No source edits followed this check. All 10 acceptance rows are closed for this bounded leaf, with coordinator acceptance pending.

Broad Lake/aggregate/design gates and committed-range checks are owned by root. This leaf is three uncommitted files with a narrow import closure, so duplicating those broad integration checks would not add distinct local evidence. Root owns the final strict design-policy base and integrated committed range. Documentation-only closure edits do not change the verified Lean proof terms.

## Proposed design entry for the coordinator

Title: Actual loader word safety from numeric memory and representable span geometry.

Decision and rationale: establish source scalar safety on arbitrary fitting numeric memory before invoking the existing compiler preservation theorem. Fitting instruction encodings cannot by themselves establish subtraction order, nonzero divisors, shift amounts, arithmetic results, or a failed second address. The source predicate inspects evaluated intermediate states; the primitive conclusions retain each executed instruction and every prefix on the same run as values, receipts, and cost.

Rejected alternatives: requiring all reads to succeed; assuming a blanket list of fitting arithmetic results; constructing the concatenation of two complete physical words; dropping missing-cell addresses; or combining existential witnesses from different hosted runs. Each would omit an assigned operational obligation or hide the hard numeric step.

Consequences: the generic span source needs width >= 2 and len < width, while fixed setup source needs width >= 8. Generic machine placement has explicit code/end-PC bounds; canonical runs discharge them at the existing `wordWidth`. No ISA, source loader, payload, public width function, or runtime cost model is changed. The checked crossing path uses the existing mask-before-left-shift order. Evidence is the full propositions and same-object chain above plus boundary consumers.

No new workflow/process design was introduced. The build-slot discipline, frozen matrix, bounded checks, and coordinator-owned integration follow the existing workflow. The proof-performance repairs are implementation technique, not a change to those rules.

## Proof digestion and downstream boundary

Conceptually, this leaf turns the concrete span and metadata source routines into word-safe primitive executions. In plain language, every executed scalar operation, register value, result, attempted address, and code field fits the declared machine word; if a numeric cell is absent, the failure is real and later prefixes remain safe. Values, ordered receipts, and fixed instruction budgets refer to that same execution.

Live assumptions are explicit: entry registers/status fit; span position fits and len is strictly below width; arbitrary hosted code has fitting fields and an end PC. The canonical consumers remove memory/minimum-width/static-bank obligations without any readiness or presence condition. The next skeptical check is to inspect the actual mask-before-shift source order, the second address before lookup, and the source-to-run equalities—not to assume a mathematical decoder was charged as one instruction. Those checks are discharged here.

The lead still derives the full controller/location/rank/select arithmetic invariants and whole-reader `Block.Safe`. That is the frozen downstream boundary: this leaf closes the two actual loader routines, not the entire query capstone.
