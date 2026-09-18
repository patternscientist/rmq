# OPT-1-R1 inherited proof and object identity

This is a source-evidence inventory for OPT-1-R1, not a fresh compilation,
production replay, independent audit or coordinator acceptance receipt.
The repair preserves the proof construction and changes its replay certification.

- Governance: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
- Original row freeze: `1f3a4199eaa95324cd1daaadbab89340ca8392c4`.
- Proof/history baseline: `aecf4a580c591e8f694a3699e19e843198089194`.
- Final source evidence: the exact `CandidateRef` in the preservation receipt.
- Fresh compilation/source-profile linkage and the actual repaired runtime and
  certificate campaigns have separate receipts; this file does not supply them.

## Immutable source inventory

The baseline has 12 Optimization files, 55 shared Packed files, the single
`RMQ/Validation/PackedOptimized.lean` validator, three optimized axiom scripts,
and 439 existing OPT-1 history files. The preservation checker compares the
entire baseline path/mode/object map with the candidate, rejects omission and
changed modes or blobs, and admits additional paths in those protected scopes
only below `docs/internal/extensions/opt1/repair-r1/`.

| Surface | Baseline Git object |
| --- | --- |
| `RMQ/Core/WordRAM/Optimization` | tree `7a1747d7a24a5e852d2ff9b70b8cc7331f21ece4` |
| `RMQ/Core/WordRAM/Packed` | tree `3d79805dd4016cb6388b57076af46fa52175856c` |
| Original OPT-1 history | tree `29cf42f9e52c52f89ea019d7cff8e9b0811e578a` |
| `Optimization/Certificate.lean` | blob `9d47713c26a491934ab17526750b08761c6afa87` |
| `Optimization/Capstone.lean` | blob `7eeebe68bbd2ea3077fe825a5b01462e1b8f09a4` |
| `Optimization/Consumers.lean` | blob `7a78c403e548df7ba7e7782ab081f08c4f4ad32b` |
| `RMQ/Validation/PackedOptimized.lean` | blob `dfc6b3639a7224ec900c05736f512d28cfd21088` |
| Original acceptance matrix | blob `bd5d0eb38fd4a301eb89b027fcc434fc18dbee75` |
| `certificate-replay/FIELDS.json` | blob `3760470717560aafc5ae4652522eff1953d001e7` |
| `AXIOM_ROOTS.json` | blob `4c9314d23730f318c1a4f99ca13e2156912f277b` |

The historical matrix as a whole has later append-only evidence after its
original freeze. Its entire candidate blob is compared with the proof/history
baseline, while all 35 complete frozen row-content byte strings are compared
with the original row freeze. Each row starts at its leading pipe and ends at
its trailing pipe; its physical LF or CRLF terminator is outside that string.
No row whitespace, Unicode, punctuation or column content is normalized.
Strict UTF-8 decoding, duplicate/missing/unknown ID rejection and direct byte
equality precede the separately recorded SHA-256 values. The mojibake control
is an independent negative check and never substitutes for equality.

## Same-object construction and full guards

The following are the actual definitions in `Optimization/Query.lean`:

```lean
def compactQuerySource : Block := .seq querySource (.exit 3)
def compactQueryFresh : Nat := queryRegisterCount
def compactQueryProgram : Program := compactAt compactQuerySource compactQueryFresh 0 0
def compactQueryBudget : Nat := compactBound compactQuerySource
def compactQueryRegisterCount : Nat := compactQueryFresh + 2 * compactDepth compactQuerySource
def compactQueryScratchWords : Nat := compactQueryRegisterCount + 3
def compactQueryProgramWords : Nat := (compactQueryProgram.map Instruction.encoding).flatten.length
def compactQueryCompleteRho : Nat → Nat :=
  allocationWithMachineRho compactQueryProgramWords compactQueryScratchWords

def compactQueryRun (memory : Memory) (n left right : Nat) : Run :=
  run memory compactQueryProgram compactQueryBudget (initialState n left right)
```

In the mappings below, `M := buildMemory xs`, `P := compactQueryProgram`,
`B := compactQueryBudget`, `I := initialState xs.length left right`,
`W := wordWidth xs.length`, and `R := run M P B I`. These abbreviate the
existing definitions; they introduce no sibling construction.

The counted allocation has the literal chain:

```lean
def shapeMemory (shape : CartesianShape) : List Nat :=
  repackWords (metadata shape) (wordWidth shape.size) (packedReviewerMemory shape)

def buildMemory (xs : List Int) : List Nat :=
  shapeMemory (SuccinctClassic.cartesianShape xs)

def allocationWithMachineRho (programWords scratchWords n : Nat) : Nat :=
  allocationRho n + (programWords + scratchWords) * wordWidth n
```

The space consumer counts that same `M`, the actual flattened encoding of
`P`, and the entire declared bank plus three machine-state words. The stored
metadata and packed payload remain in `M`. The program is fixed independently
of `xs`; no input-specific data is moved into uncounted code.

`CompactPackedQueryCapstone : Prop` has a premise-free inhabitant
`compactPackedQueryCapstone_holds`. Every mandatory field `f` has both
`CertificateConsumers.f_expectedType (certificate : CompactPackedQueryCapstone)`
at an independently written type and `f_canonical` at the same type, using
`f_expectedType compactPackedQueryCapstone_holds`. All 39 full types are
copied verbatim from the unchanged FIELDS inventory below and byte-checked.
The complete field declarations and producer initializers remain in the
pinned `Certificate.lean` and `Capstone.lean` blobs above.

The domain split is unchanged. `natContract` quantifies every `List Int`
and both natural endpoints, returning `none` outside
`ValidRange xs left right`, whose existing half-open condition is
`left < right ∧ right ≤ xs.length`. Raw canonical result/halt/refinement
theorems have no size/readiness assumption. Physical safety fields require
only `left < 2 ^ W` and `right < 2 ^ W`, and use the same `M/P/B/I/W`.
`validInputs` proves those representability conditions from `ValidRange`.
Representable invalid inputs halt with packet zero and no reads. No guard
silently selects a different allocation or execution.

## Compiler-to-execution evidence

The branch recurrence is skip zero, action/exit one, sequence sum,
`ifZero` maximum of `1 + zero` and `2 + nonzero`, and repeat count times
body bound. `compile_realizes_branchBound` constructs actual transitions.
Its adequacy consumer states:

```lean
theorem compiled_run_bound_and_fuel_eq (memory : Memory) (block : Block)
    (s : State) (hpc : s.pc = 0) (a b : Nat)
    (ha : branchBound block ≤ a) (hb : branchBound block ≤ b) :
    (run memory (block.compileAt 0) a s).steps ≤ branchBound block ∧
    run memory (block.compileAt 0) a s = run memory (block.compileAt 0) b s
```

The producer proves the witnessed segment stops at a terminal fetch. Both
fuel settings equal that complete segment. Instantiation at
`.seq querySource (.exit 3)` proves the original adequately fuelled query
bound `150739` and full original/reduced-fuel `Run` equality for arbitrary
numeric memory and all `n/left/right`, including malformed metadata and
failed loads. It is not the tautological bound of a truncated run by its fuel.

Compact positive repetition emits two fresh-register constants, a zero test,
one body copy at the next scratch depth, decrement and backward jump: five
control instructions plus the body. Zero repetition emits no code. The
existing primitive instruction constructors and `execute` are unchanged.
`compactAt_length` gives the emitted list length; `compactAt_encoding_length`
counts all actual opcode/operand words. The checked concrete values are
`P.length = 212964`, flattened encoding length `722339`, `B = 151978`,
register bank `8273` and scratch `8276`; `P.length < queryProgram.length`.
The original complete-query bound remains `150739`.

The compact simulation uses this exact relation:

```lean
def CompactRealizes (memory : Memory) (program : Program) (observed : Nat)
    (s : State) (expected : Evaluation) (finish budget : Nat) : Prop :=
  ∃ final transitions,
    RunsTo memory program s final transitions ∧
    DataAgreesBelow observed (Data.ofState final) expected.final ∧
    transitions.filterMap (·.receipt) = expected.reads ∧
    transitions.length ≤ budget ∧
    (final.status = .running → final.pc = finish)
```

`DataAgreesBelow bound a b` means equal status and equal registers for every
`r < bound`. `BlockRegistersBelow fresh block` includes every source operand,
including address registers, branch conditions, halt registers and dormant
bodies. The generic realization consumer requires `s.pc = base`, this full
operand condition, and
`HostedAt program base (compactAt block fresh depth base)`. It concludes an
actual `RunsTo` segment with final status/source-register equality, exact
ordered receipts, bounded transition count, and the correct final PC when
still running. Body evaluation is rebased at each actual entry state;
frames preserve parent counters. Global word fit is a separate obligation
and is not inferred from finite register agreement.

`compact_compile_run` consumes that realization at any
`fuel ≥ compactBound block`, preserving evaluator data/receipts, proving the
actual count bound, and proving no next primitive step exists. Appending the
halt on an observed register gives `compact_compile_with_halt`, preserving
earlier halt/fault and ordered attempted replies. `compactQueryRun_refines_source`
instantiates this at `querySource`, `compactQueryFresh` and output register 3.
Its conjunction gives source-derived result, read equality, bound and stopped
status. `compactQueryRun_original_observations` composes that relation with
the original source refinement. `compactQueryRun_fuel_eq` extends only an
already stopped complete compact run. The 39-field capstone consumes these
results explicitly through `arbitraryMemoryObservations`, `completedExecution`
and `adequateFuel`, in addition to `stepBound`.

## Returned values, occurrence order, physical backing and word model

`Primitive.execute.load` reads `memory[s.regs address]?`, writes its returned
value to the destination register or faults, and records precisely that
address/reply. Arithmetic, comparisons, branches and halt use those register
values. There is no certificate input to execution and no semantic answer
computed for a decorative read pass. `Run.result` reads final halted status;
`Run.reads` filters actual transitions. The supplied-memory agreement field
equates complete `Run` objects, therefore including result, cost and ordered
receipts, under agreement at the canonical attempted read addresses.

`positionalReadBacking` retains transition index, producing instruction,
actual prefix pre-state, execution equation, address register and reply. It
does not reduce an occurrence claim to `List.Mem`. The full exact field type
below is unguarded; `readWidth` adds endpoint representability, and
`noFailedLoads` supplies successful replies on valid ranges. Repeated equal
receipts retain their order and multiplicity.

`programFieldsFit` covers every instruction in `P`, including dormant code.
`Instruction.Fits width i` is
`∀ operand ∈ i.encoding, operand < 2 ^ width`; encoding includes every opcode,
operation tag, register identifier, count/immediate and control target.
`allocationAddressesFit` includes `address = M.length`, the dead sentinel.
Actual indexed read and transition safety bound dynamic addresses and results
against the same `2 ^ W`, not merely host array capacity.

`wordWidth n` is independent of the query endpoints and satisfies
`Nat.log2 (n + 2) + 1 ≤ wordWidth n ≤ 192 * (Nat.log2 (n + 2) + 1)`.
`LittleOLinear compactQueryCompleteRho` and literal complete capacity include
the code, scratch and same physical store at this width. The primitive RAM
cost model, Lean List/Array execution, proof-only transition observations,
payload bits and measured validation timings remain separate. Neither
execution upper bound is claimed attained or a native runtime measurement.

## Accepted and mutated predicates

For compiler fixtures, the accepted observation predicate is exactly
`actual.final.status == fixture.expected && actual.reads == fixture.receipts`,
where `actual := runArray fixture.memory program.toArray fuel fixture.state`.
The independent `Block.eval` result must agree with those literal fixture
expectations before the actual compiler observation is checked. C05 expects
`.halted 7`, three ordered copies of `⟨0, some 7⟩`, and 16 steps. N01 changes
instruction 2 to `.branchZero 8 0`; N02 changes instruction 0 to `.constant 8 0`;
N03 uses zero fuel; N04 emits with fresh origin 0, colliding with source
registers. The same memory/state/observation predicate applies to the positive
and mutated executions. They must reject at that observation predicate before
later step/frame checks. The repaired runtime output classifier is a separate
production obligation and must recognize only its admitted exclusive diagnostic.

For field `f`, `P_f` is the full fixed ExpectedType below. The accepted
consumer elaborates at `P_f` by projecting `certificate.f`; its canonical
companion consumes the capstone inhabitant. A D mutation deletes the field
and initializer. A W mutation replaces the producer proposition by `True`
and its initializer by `True.intro`, while leaving the consumer at `P_f`.
Both altered producer modules must elaborate before consumer rejection at
the exact selected field is credited. This is a checked dependency failure,
not a claim to prove `¬ True`. The exact 80-case production registry has
two accepts and 39 deletion/weakening pairs. All 78 consumers stay fixed.

The semantic campaigns remain finite non-vacuity controls, while the unchanged
universal theorem types establish their stated domains. In particular, whole-run
agreement does not assert that every conceivable corruption changes an answer;
Q09 separately supplies a concrete changed-answer malformed-metadata control.
Source/token/provenance failure cannot be counted as a semantic field rejection.

## Complete inherited row mapping

Every named field below refers to both its generic and canonical consumers,
whose exact full propositions follow in the appendix. All object abbreviations
and quantifier/guard conventions are fixed above. Historical campaign receipts
remain historical; fresh R1 checker/profile/runtime/certificate evidence is
required wherever the production path changed.

| Frozen ID | Exact producer/consumer chain and boundary |
| --- | --- |
| REQ-OPT-BUDGET | Actual branch RunsTo witness → compiled_run_bound_and_fuel_eq → branchSensitiveQueryBound and reducedFuel_queryRun_eq → originalExecutionBound/originalReducedFuel. Arbitrary memory and all n/endpoints; full Run equality, not truncated fuel. |
| REQ-OPT-COMPILE | compactAt ordinary emitted controls → compact_realizes → compact_compile_run/compact_compile_with_halt → completedExecution/adequateFuel and arbitraryMemoryObservations. compactAt_length/encoding_length → programLength/encodedProgramLength/programReduction/emittedProgram. Fresh source-register condition and hosted absolute targets are explicit. |
| REQ-OPT-RUN | Arbitrary-memory result/ordered-receipt equality → canonical result/halt/invalidGuard/natContract/leftmost. Same M/P/B/I/W → guarded program, indexed transition, prefix, read/address/word safety. Failed loads and duplicate receipts are retained. |
| REQ-OPT-SPACE | Literal flattened Instruction.encoding and finite bank plus three state words → completeCapacity. completeResidualLittleO and unusedRegisters at every fuel, together with registerCount/scratchCount, account for both fresh counters. |
| REQ-OPT-CONSUMER | Premise-free compactPackedQueryCapstone_holds supplies 39 mandatory full propositions; each has fixed generic/canonical consumers. Fresh production 80-case dependency replay remains separate from source identity. |
| CHK-OPT-CONTROLS | Unchanged validator imports the actual Optimization capstone/emitter. It supplies 13 compiler positives, 10 query positives and four same-predicate compiler mutations. Fresh repaired production execution must retain all exact outcomes. |
| REPLAY-EXACT-REGISTRY | Runtime exact27 and certificate exact80 (A01,A02,D01,W01 through D39,W39); declared and executed lists must agree. The separate preservation registry also pins every executed control. |
| REPLAY-SELECTOR-NONVACUITY | Actual script/environment boundary distinguishes omission from bound empty/blank, unknown/malformed/duplicate selectors; a focused run executes exactly one declared case. Changed production entry points need fresh controls. |
| REPLAY-SUBPROCESS-DEADLINE | Existing owned_process_tree implementation supervises real tool children with positive bounds, raw streams, exits and cleanup receipts. Finally restoration checks actual bytes/index. Windows evidence cannot certify unexecuted POSIX behavior. |
| CHK-OPT-DEVELOPMENT | Unchanged exact proof/consumer blobs permit reuse of their checked theorem evidence. Changed script/profile implementation requires fresh narrow controls and actual source/artifact compilation linkage; no implicit fallback build in a negative stage. |
| CHK-OPT-FINAL | Final source/row identity, required Lake build, explicit new consumer/capstone import, exact production registries, trust inventory and committed whitespace/design checks. Coordinator owns the separately deferred full aggregate slot. |
| CHK-OPT-TRUST | Exactly93 distinct axiom roots and shared builtin union, with two ordinary public #print axioms declarations; only standard propext/Classical.choice/Quot.sound. Final trust scans remain required and actual matches must be reported. |
| CHK-OPT-CONDITIONAL | Final report/family/digestion additions require fresh strict claim certification and applicable constant sync; unchanged Lean proof sources do not license stale report-sensitive evidence. |
| CHK-OPT-AUDIT | Independent exact-candidate audit, coordinator aggregate and coordinator disposition remain external. This source inventory does not self-accept the worker or compiler milestone. |
| INV-STORE-IDENTITY | completeCapacity/result/safety/positionalReadBacking/suppliedMemoryAgreement literally fix the same M/P/B/I/W; buildMemory → shapeMemory → repackWords chain is given above. |
| INV-VALUE-DEPENDENCY | Actual load replies write registers used by arithmetic/branch/halt; source refinement constrains result. suppliedMemoryAgreement equates full Runs. Q09 changes the returned result after metadata corruption, rather than merely changing a log field. |
| INV-SEMANTIC-NONVACUITY | CompactRealizes contains actual RunsTo transitions, status/register equality and ordered reads; source-register predicates cover actual operands, including dormant read operands. The positive and mutation compiler observation predicate is identical. |
| INV-TRACE-EXECUTION | Run.reads is the filterMap of real transitions. positionalReadBacking retains global index, producing instruction, actual folded prefix state, execution equation and physical reply. |
| INV-STORE-AGREEMENT | For all xs/supplied memory/endpoints, agreement at every attempted canonical receipt address determines equality of full runs, including result/cost/receipts and failures; no valid-range premise is hidden. |
| INV-READ-BACKING | Every indexed receipt transition is an actual load at the pre-state address register with reply M[address]?. ValidRange adds noFailedLoads, proving a successful value for each receipt. |
| INV-WORD-WIDTH | memoryWordsFit, finalStateFit, transitionSafety and readWidth use W for stored words, PC, every register, halted value and actual primitive/read results. Physical fields retain the same representability guards. |
| INV-ADDRESS-WIDTH | allocationAddressesFit includes the dead sentinel M.length. Every encoded field of every P instruction fits 2^W, and indexed dynamic safety bounds actual addresses/operands. Host in-range is insufficient. |
| INV-INSTRUCTION-ATOMICITY | Compact adds no Instruction constructor and leaves execute unchanged. Each loop constant/test/decrement/jump is an existing primitive transition charged by the simulation; native List lookup cost is not called one Lean runtime step. |
| INV-PROGRAM-ACCOUNTING | completeCapacity counts full numeric opcode/operand encoding including count constants/targets; P is query-independent. Input metadata stays in M; fresh registers and state words are counted. |
| INV-ORACLE-INDEPENDENCE | Compiler literal fixture status/receipts/steps are first checked against independent Block.eval. Query expectations use literal indices and scanWindow; route checks use Cartesian closes and logical trace rather than the compact result. |
| INV-VALIDATION-REACH | Validator invokes actual compactAt/P through runArray and compares compiler fixtures with list run; runArray_toArray proves full Run equality for every memory/program/fuel/state. Predecessor-only validation is insufficient. |
| INV-ALL-SIZE | natContract is unconditional over every List Int and natural endpoints, guarded only by ValidRange in its result. Canonical raw correctness has no readiness threshold; physical safety only assumes endpoint representability. |
| INV-PROOF-SEPARATION | CompactPackedQueryCapstone is Prop; executable emission/run/query definitions consume no certificate, proof-carried answer or semantic oracle. |
| INV-NO-SYNTHETIC | Each receipt is produced by actual execute.load at its retained prefix/instruction on M; neither post-hoc trace construction nor decorative rereads support the theorem. |
| INV-CATEGORY-SEPARATION | Program212964 instructions, encoding722339 numeric words, compact bound151978, original bound150739, scratch8276 and bit capacity are distinct. Timings validate execution but are not model bounds or attainment witnesses. |
| INV-PUBLIC-COMPOSITION | One inhabited 39-field record fixes M/P/B/I/W throughout. validInputs connects ValidRange to physical guards; representable invalid inputs use the same run returning zero and no reads. |
| INV-CERTIFICATE-ANTI-BYPASS | All39 exact field propositions are independently stated by generic/canonical typed consumers. D/W producer modules must compile before that field's fixed consumer rejects; changing a constructor alone cannot supply the missing exact proposition. |
| INV-MUTATION-REPRODUCIBILITY | Versioned runtime/certificate registries generate all exact cases and restore isolated sources/artifacts. R1 requires fresh repaired production campaigns, profile identity, full raw results and restoration; historical prose or setup errors cannot close this row. |
| INV-GLOBAL-PHYSICAL-MACHINE | One M contains the metadata and full repacked payload. orderedLogicalRefinement covers the metadata prefix plus the entire logical query trace, while positional backing and completeCapacity concern every read of that same M. |
| INV-WIDTH-SCALING | widthBounds gives the same query-independent logarithmic W for data/code/scratch/stored values/sentinels/operands/actual primitive safety. completeResidualLittleO is tied to that exact counted construction. |

## Axiom checker and verification use

`scripts/packed_optimized_axiom_union.lean` checks existence/distinctness of
93 roots, visits every root using one shared builtin collector traversal,
and reports the exact union. The roots comprise 15 public/producer declarations
plus 78 field consumers. This is not an individual axiom distribution for
each declaration. It also retains the ordinary commands:

```lean
#print axioms RMQ.SuccinctFinal.PackedWordRAM.Optimization.branchSensitiveQueryBound
#print axioms RMQ.SuccinctFinal.PackedWordRAM.Optimization.compactPackedQueryCapstone_holds
```

`scripts/packed_optimized_axiom_check.ps1` requires exactly93 unique expected
roots, one union, both and only those two standard prints, and print-axiom
inclusion in the union. The admitted axiom set is
`propext`, `Classical.choice`, `Quot.sound`. It invokes pinned Lean 4.22.0
with `-j1`, 180 seconds and a 2 MiB output ceiling. The historical shared
collector run took 8.710 seconds; a new final receipt must identify its own
tree, compiled imports and measured outcome.

The unchanged checker writes into the historical composition-development
directory. R1 must run that checker in a private reproduction checkout and
retain its new receipt in the repair evidence, preserving original history.
No source hash by itself proves compilation or source/artifact linkage.

The preservation API is `preservation/check.ps1 -CandidateRef <exact40SHA>
-RepoRoot <checkout> -OutputDirectory <new directory>`. `-SelfTestOnly`
executes its narrow registry and live row/type checks before a repair matrix
has been committed; it explicitly does not certify candidate repair blobs.
Final mode requires committed old/new matrix and proof-identity artifacts,
compares protected candidate objects/index/live Git differences, and records
before/after raw hashes. Run final mode after the candidate commit, then
retain the receipt in a later evidence-only commit if necessary, identifying
the exact candidate it checked. That receipt is not silently relabeled as a
check of its later containing commit.

## Verbatim 39-field ExpectedType appendix

Each fenced payload below is exactly the decoded strict-UTF-8 ExpectedType
string from the baseline FIELDS.json, without type inference from a mutable
certificate. The checker compares its UTF-8 bytes directly with that pinned
Git blob and verifies both consumer name sets. Source identity still requires
the complete immutable Certificate/Capstone/Consumers blobs, not only this
documentary appendix.


### allocationResidualLittleO

<!-- OPT1-R1-FIELD-allocationResidualLittleO-BEGIN -->
```lean
LittleOLinear allocationRho
```
<!-- OPT1-R1-FIELD-allocationResidualLittleO-END -->

### completeResidualLittleO

<!-- OPT1-R1-FIELD-completeResidualLittleO-BEGIN -->
```lean
LittleOLinear compactQueryCompleteRho
```
<!-- OPT1-R1-FIELD-completeResidualLittleO-END -->

### widthBounds

<!-- OPT1-R1-FIELD-widthBounds-BEGIN -->
```lean
∀ n, Nat.log2 (n + 2) + 1 ≤ wordWidth n ∧
    wordWidth n ≤ 192 * (Nat.log2 (n + 2) + 1)
```
<!-- OPT1-R1-FIELD-widthBounds-END -->

### dataCapacity

<!-- OPT1-R1-FIELD-dataCapacity-BEGIN -->
```lean
∀ xs : List Int, (buildMemory xs).length * wordWidth xs.length ≤
    2 * xs.length + allocationRho xs.length
```
<!-- OPT1-R1-FIELD-dataCapacity-END -->

### completeCapacity

<!-- OPT1-R1-FIELD-completeCapacity-BEGIN -->
```lean
∀ xs : List Int,
    ((buildMemory xs).length + (compactQueryProgram.map Instruction.encoding).flatten.length +
      (compactQueryRegisterCount + 3)) * wordWidth xs.length ≤
        2 * xs.length + compactQueryCompleteRho xs.length
```
<!-- OPT1-R1-FIELD-completeCapacity-END -->

### memoryWordsFit

<!-- OPT1-R1-FIELD-memoryWordsFit-BEGIN -->
```lean
∀ (xs : List Int) word, word ∈ buildMemory xs → word < 2 ^ wordWidth xs.length
```
<!-- OPT1-R1-FIELD-memoryWordsFit-END -->

### allocationAddressesFit

<!-- OPT1-R1-FIELD-allocationAddressesFit-BEGIN -->
```lean
∀ (xs : List Int) address, address ≤ (buildMemory xs).length →
    address < 2 ^ wordWidth xs.length
```
<!-- OPT1-R1-FIELD-allocationAddressesFit-END -->

### programFieldsFit

<!-- OPT1-R1-FIELD-programFieldsFit-BEGIN -->
```lean
∀ n instruction, instruction ∈ compactQueryProgram → instruction.Fits (wordWidth n)
```
<!-- OPT1-R1-FIELD-programFieldsFit-END -->

### budgetExact

<!-- OPT1-R1-FIELD-budgetExact-BEGIN -->
```lean
compactQueryBudget = 151978
```
<!-- OPT1-R1-FIELD-budgetExact-END -->

### programLength

<!-- OPT1-R1-FIELD-programLength-BEGIN -->
```lean
compactQueryProgram.length = 212964
```
<!-- OPT1-R1-FIELD-programLength-END -->

### encodedProgramLength

<!-- OPT1-R1-FIELD-encodedProgramLength-BEGIN -->
```lean
(compactQueryProgram.map Instruction.encoding).flatten.length =
    722339
```
<!-- OPT1-R1-FIELD-encodedProgramLength-END -->

### programReduction

<!-- OPT1-R1-FIELD-programReduction-BEGIN -->
```lean
compactQueryProgram.length < queryProgram.length
```
<!-- OPT1-R1-FIELD-programReduction-END -->

### emittedProgram

<!-- OPT1-R1-FIELD-emittedProgram-BEGIN -->
```lean
compactQueryProgram = compactAt compactQuerySource compactQueryFresh 0 0
```
<!-- OPT1-R1-FIELD-emittedProgram-END -->

### originalExecutionBound

<!-- OPT1-R1-FIELD-originalExecutionBound-BEGIN -->
```lean
∀ memory n left right, (queryRun memory n left right).steps ≤ 150739
```
<!-- OPT1-R1-FIELD-originalExecutionBound-END -->

### originalReducedFuel

<!-- OPT1-R1-FIELD-originalReducedFuel-BEGIN -->
```lean
∀ memory n left right,
    run memory queryProgram 150739 (initialState n left right) = queryRun memory n left right
```
<!-- OPT1-R1-FIELD-originalReducedFuel-END -->

### arbitraryMemoryObservations

<!-- OPT1-R1-FIELD-arbitraryMemoryObservations-BEGIN -->
```lean
∀ memory n left right,
    (compactQueryRun memory n left right).result = (queryRun memory n left right).result ∧
    (compactQueryRun memory n left right).reads = (queryRun memory n left right).reads
```
<!-- OPT1-R1-FIELD-arbitraryMemoryObservations-END -->

### completedExecution

<!-- OPT1-R1-FIELD-completedExecution-BEGIN -->
```lean
∀ memory n left right,
    (compactQueryRun memory n left right).final.status ≠ .running
```
<!-- OPT1-R1-FIELD-completedExecution-END -->

### adequateFuel

<!-- OPT1-R1-FIELD-adequateFuel-BEGIN -->
```lean
∀ memory n left right fuel, compactQueryBudget ≤ fuel →
    run memory compactQueryProgram fuel (initialState n left right) =
      compactQueryRun memory n left right
```
<!-- OPT1-R1-FIELD-adequateFuel-END -->

### registerCount

<!-- OPT1-R1-FIELD-registerCount-BEGIN -->
```lean
compactQueryRegisterCount = 8273
```
<!-- OPT1-R1-FIELD-registerCount-END -->

### scratchCount

<!-- OPT1-R1-FIELD-scratchCount-BEGIN -->
```lean
compactQueryScratchWords = 8276
```
<!-- OPT1-R1-FIELD-scratchCount-END -->

### unusedRegisters

<!-- OPT1-R1-FIELD-unusedRegisters-BEGIN -->
```lean
∀ (xs : List Int) left right fuel r, compactQueryRegisterCount ≤ r →
    (run (buildMemory xs) compactQueryProgram fuel (initialState xs.length left right)).final.regs r = 0
```
<!-- OPT1-R1-FIELD-unusedRegisters-END -->

### validInputs

<!-- OPT1-R1-FIELD-validInputs-BEGIN -->
```lean
∀ (xs : List Int) left right, ValidRange xs left right →
    encodeInputs xs.length left right = some (initialState xs.length left right) ∧
      left < 2 ^ wordWidth xs.length ∧ right < 2 ^ wordWidth xs.length
```
<!-- OPT1-R1-FIELD-validInputs-END -->

### natContract

<!-- OPT1-R1-FIELD-natContract-BEGIN -->
```lean
∀ (xs : List Int) left right,
    compactQueryNat (buildMemory xs) xs.length left right =
      if ValidRange xs left right then some (scanWindow xs left (right - left)) else none
```
<!-- OPT1-R1-FIELD-natContract-END -->

### leftmost

<!-- OPT1-R1-FIELD-leftmost-BEGIN -->
```lean
∀ (xs : List Int) left right index,
    compactQueryNat (buildMemory xs) xs.length left right = some index → LeftmostArgMin xs left right index
```
<!-- OPT1-R1-FIELD-leftmost-END -->

### result

<!-- OPT1-R1-FIELD-result-BEGIN -->
```lean
∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).result =
      some (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value)
```
<!-- OPT1-R1-FIELD-result-END -->

### halt

<!-- OPT1-R1-FIELD-halt-BEGIN -->
```lean
∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).final.status =
      .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value)
```
<!-- OPT1-R1-FIELD-halt-END -->

### invalidGuard

<!-- OPT1-R1-FIELD-invalidGuard-BEGIN -->
```lean
∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length → ¬ ValidRange xs left right →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).result = some 0 ∧
      (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).reads = []
```
<!-- OPT1-R1-FIELD-invalidGuard-END -->

### stepBound

<!-- OPT1-R1-FIELD-stepBound-BEGIN -->
```lean
∀ (xs : List Int) left right,
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).steps ≤ compactQueryBudget
```
<!-- OPT1-R1-FIELD-stepBound-END -->

### categoryPartition

<!-- OPT1-R1-FIELD-categoryPartition-BEGIN -->
```lean
∀ (xs : List Int) left right,
    let actual := run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)
    actual.steps = actual.categoryCount .memoryRead + actual.categoryCount .registerWrite +
      actual.categoryCount .arithmetic + actual.categoryCount .comparison +
      actual.categoryCount .branch + actual.categoryCount .control
```
<!-- OPT1-R1-FIELD-categoryPartition-END -->

### finalStateFit

<!-- OPT1-R1-FIELD-finalStateFit-BEGIN -->
```lean
∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).final.Fits (wordWidth xs.length)
```
<!-- OPT1-R1-FIELD-finalStateFit-END -->

### transitionSafety

<!-- OPT1-R1-FIELD-transitionSafety-BEGIN -->
```lean
∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition),
      (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).transitions[index]? = some t →
      Instruction.Safe (wordWidth xs.length) t.before t.instruction ∧ t.after.Fits (wordWidth xs.length)
```
<!-- OPT1-R1-FIELD-transitionSafety-END -->

### prefixSafety

<!-- OPT1-R1-FIELD-prefixSafety-BEGIN -->
```lean
∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ fuel, fuel ≤ compactQueryBudget →
      (run (buildMemory xs) compactQueryProgram fuel (initialState xs.length left right)).final.Fits (wordWidth xs.length)
```
<!-- OPT1-R1-FIELD-prefixSafety-END -->

### readWidth

<!-- OPT1-R1-FIELD-readWidth-BEGIN -->
```lean
∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition) (receipt : Receipt),
      (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).transitions[index]? = some t →
      t.receipt = some receipt →
      receipt.address < 2 ^ wordWidth xs.length ∧ receipt.reply = (buildMemory xs)[receipt.address]? ∧
        (∀ value, receipt.reply = some value → value < 2 ^ wordWidth xs.length)
```
<!-- OPT1-R1-FIELD-readWidth-END -->

### positionalReadBacking

<!-- OPT1-R1-FIELD-positionalReadBacking-BEGIN -->
```lean
∀ (xs : List Int) left right index (t : Transition) (receipt : Receipt),
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).transitions[index]? = some t →
    t.receipt = some receipt →
    t.before = (run (buildMemory xs) compactQueryProgram index (initialState xs.length left right)).final ∧
      t.before.status = .running ∧ compactQueryProgram[t.before.pc]? = some t.instruction ∧
      execute (buildMemory xs) t.instruction t.before = (t.after, t.receipt) ∧
      ∃ dst addrReg, t.instruction = .load dst addrReg ∧
        receipt.address = t.before.regs addrReg ∧ receipt.reply = (buildMemory xs)[receipt.address]?
```
<!-- OPT1-R1-FIELD-positionalReadBacking-END -->

### orderedLogicalRefinement

<!-- OPT1-R1-FIELD-orderedLogicalRefinement-BEGIN -->
```lean
∀ (xs : List Int) left right,
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).reads =
      if ValidRange xs left right then
        (List.range 174).map (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ++
          logicalTraceReads (SuccinctClassic.cartesianShape xs) (buildMemory xs)
            (SuccinctClassic.queryTraceResult xs left right).trace
      else []
```
<!-- OPT1-R1-FIELD-orderedLogicalRefinement-END -->

### logicalReadOnly

<!-- OPT1-R1-FIELD-logicalReadOnly-BEGIN -->
```lean
∀ (xs : List Int) left right,
    ReadOnlyTrace (SuccinctClassic.queryTraceResult xs left right).trace
```
<!-- OPT1-R1-FIELD-logicalReadOnly-END -->

### suppliedMemoryAgreement

<!-- OPT1-R1-FIELD-suppliedMemoryAgreement-BEGIN -->
```lean
∀ (xs : List Int) (memory : Memory) left right,
    (∀ receipt ∈ (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).reads,
      memory[receipt.address]? = (buildMemory xs)[receipt.address]?) →
    run memory compactQueryProgram compactQueryBudget (initialState xs.length left right) =
      run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)
```
<!-- OPT1-R1-FIELD-suppliedMemoryAgreement-END -->

### specResult

<!-- OPT1-R1-FIELD-specResult-BEGIN -->
```lean
∀ (xs : List Int) left right, ValidRange xs left right →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).result =
      some (scanWindow xs left (right - left) + 1)
```
<!-- OPT1-R1-FIELD-specResult-END -->

### noFailedLoads

<!-- OPT1-R1-FIELD-noFailedLoads-BEGIN -->
```lean
∀ (xs : List Int) left right, ValidRange xs left right →
    ∀ receipt ∈ (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).reads,
      ∃ value, receipt.reply = some value
```
<!-- OPT1-R1-FIELD-noFailedLoads-END -->
