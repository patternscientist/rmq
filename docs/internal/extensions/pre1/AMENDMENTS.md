# PRE-1 append-only contract amendments

Version 1, proposed under the explicit PRE-1 authorization. Historical plan and JSON bytes remain unchanged. These amendments are part of the mandatory independent contract audit; this author ledger does not record coordinator acceptance.

Base: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`. Exact old wording is copied below, not reconstructed from memory.

## O-UNIF

Exact old plan row (C.2):

```text
| O-UNIF | **Program uniformity** — single closed constant, length `rfl`-pinned, static program bits `< \|payload(n)\|` | FK-5 | `R1 [B, FATAL]` |
```

Replacement: One closed finite program for all xs, including empty input; exact literal instruction and encoded-word counts; all code words counted at the declared width. Any residual absorption is eventual, never an all-size strict inequality. Size/shape-dependent families fail the actual Uniform predicate.

Rationale and consequence: The old plan row drops the eventual n>=n0 guard of R1. A strict gap against a 2n core is false at n=0, while PQ1 explicitly counts its large fixed code with a 32-bit width floor. Fixed code plus bounded exhaustive operand syntax prevents unbounded per-size tables without pretending small-input code is smaller than data.

## O-WORKCAP

Exact old plan row (C.2):

```text
| O-WORKCAP | **Reflected ISA with a literal per-instruction work cap.** The interpreter must be DATA, not a Lean function: `inductive Prim` over `constZero/succ/add/sub/mulConst/divConst/lt/le/eq/getBit/setBit`; constructor-exhaustive `Prim.constants` and `BInstr.semantics`, no wildcard; and three theorems, of which `bstep_reflects : forall i s, bstep i s = interpretPrims i.semantics s` is the one that stops `semantics` from being a decoration, `semantics_cap : forall i, (i.semantics).length <= primCap` with `primCap` a **literal**, and **`prim_const_cap : forall i, forall p in i.semantics, forall c in p.constants, c < 2 ^ wordBits`** -- the row that stops the payload being smuggled in `mulConst (c : Nat)` / `divConst (c : Nat)` constants, which `O-UNIF`'s program-bit budget does not see because it bounds the PROGRAM, not the interpreter. `Prim` carries **no table-lookup constructor and no unbounded `Nat` payload**, and `R1`'s budget extends to `isaBits + progBits < payloadBits`. | FK-3 | `R2 [A AND B, FATAL]` |
```

Replacement: Finite numeric-word Prim data, exhaustive opcode/operand/constant cases, actual bstep reflection, literal singleton cap 1, Operand=Fin(2^32), and constants_fit_width for every W>=32. Preserve PQ1 scalar arithmetic/control, add one-cell reserve and separately charged store, and separately named key-read/comparison-oracle operations.

Rationale and consequence: The old getBit/setBit vocabulary and mulConst Nat wording are superseded by the accepted numeric-word machine. Variable-width initialization or table generation is not one operation. Primitive operations are definitions, not callbacks; freezing the evaluator and checking reflection preserves the anti-macro intent.

## O-POINTWISE

Exact old plan row (C.2):

```text
| O-POINTWISE | **Pointwise input encoding at fixed width** — `REQ-BLD-08`, the third inherited contract-B row R11 names. Also carries `R1`'s header clause: the input length arrives in a register read from a pinned header cell, `(encodeInput xs).readWord? inputSegment 0 = some (encodeInt wordBits xs.length)`, with the element cells shifted by one. v2's C1 had the header clause; v5 and v6 both lost it | — | `R11 [BOTH]`, `R1` |
```

Replacement: The header is unsigned: encodeInput width xs 0=some xs.length. Cell i+1 is (xs[i]?).map(encodeInt width). encodeInt is biased signed encoding for keys only. Zero initial registers must obtain the header through the actual load; missing header faults for all lengths.

Rationale and consequence: Biasing a signed key and representing an unsigned length are distinct encodings. Applying the biased key encoding to the header would cause the read register to contain an offset length. Full pointwise, width, order and all-size satisfiability obligations remain; input cost is explicit.

## O-FIREWALL

Exact old plan row (C.2):

```text
| O-FIREWALL | **Import firewall, CI-enforced** — closure pinned to `{Cost, RAM, WordRAM}` | — | **Contract B already carries this as `REQ-BLD-13`**; it is why FK-2 does not survive B. Retained as an explicit obligation so the property is named rather than inherited. `R5` is the contract-A mirror and is **not** the basis here |
```

Replacement: Primitive and Input directly import Std only; Model imports those two construction modules. Exact transitive import checks and frozen evaluator-byte manifest are production guards. Semantic/control/conservative bridges remain outside that closure. Future program/run modules require an explicit reviewed closure extension.

Rationale and consequence: The historical Cost/RAM/WordRAM closure is a predecessor-specific path set. PQ1 Primitive imports Std. The new operational root can use a tighter closure; semantic negative controls must nevertheless be expressible in separate consumer modules.

## O-CONTROL

Exact old plan row (C.2):

```text
| O-CONTROL | Current-repo-shaped oracle **negative control, as a checked theorem rather than a placeholder**, with two named exhibits: `not exists ps : List Prim, ps.length <= primCap and interpretPrims ps = oracleSemantics`, and a baked-constant-table `builderProgram` variant proved to violate `R1`'s information gap. | — | `R12 [BOTH]` |
```

Replacement: Checked oracle_not_reflected negates exactly exists ps, length<=primCap and forall s, interpretPrims ps s=oracleSemantics s. The fake computes actual existing two-key Cartesian BP code in one numeric-result step. Checked baked_not_uniform negates the same Uniform predicate used by ProgramContract.

Rationale and consequence: An all-size information-gap violation is not the replacement uniformity predicate. The canonical BP-word fake tests actual result dependence without constructing a new builder; the full emitted-PQ1-cell controls remain mandatory in the later implementation. Tiny fixed constants are counted, not falsely forbidden.

## O-BITS

Exact old plan row (C.2):

```text
| O-BITS | **Bit-accounting with no fittable parameter.** `REQ-BLD-07`'s third conjunct is satisfiable by `rfl` when `paddingBits` is derived from the write log. Delete the bit-sum equation; replace it with a sequence equality in emission order (`builder_writes_canonical_words`, mapping each segment's written words onto `canonicalSegmentWords`) plus a width row (`builder_write_width`). Bit count and padding follow as corollaries and **`paddingBits` is never a free parameter** | FK-9 | `R3 [B]` |
```

Replacement: Exact ordered numeric output equality to PackedWordRAM.buildMemory xs, including 174 metadata words, old header/padding and dense repacking/new padding. No fittable padding parameter.

Rationale and consequence: The target is now the accepted PQ1 numeric allocation rather than old segmented canonicalSegmentWords 0..29. Exact equality is stronger than matching write counts or aggregate bit sums.

## O-WRITE

Exact old plan row (C.2):

```text
| O-WRITE | One shared payload sub-builder. Physical-store emission **and packed memory construction** separately costed **and joined**, with **write units stated**: bits counted in bits, or words counted in words with an exact concatenated-bit-length and an address/value replay. The units clause IS the repair — "charged writes = payload bit length" is dimensionally wrong. | — | accepted `P2-2` |
```

Replacement: Each reserve, initialization/store and emitted word write has an explicit unit; output construction and repacking both belong to the same charged run. Prove ordered words and positional address/value provenance.

Rationale and consequence: A numeric store is one word operation, not a bit. Reserve does not initialize; CleanTail forbids inherited hidden storage. Full work and output identity are still required.

## O-SCRATCH

Exact old plan row (C.2):

```text
| O-SCRATCH | **Scratch-memory row** — bounded, or its absence stated | FK-14 | `R10 [BOTH]` |
```

Replacement: Prove explicit peak temporary workspace <= Cw*n+Dw words, with all mutable extents, retained input, code and final allocation separated.

Rationale and consequence: The new authorized task removes the historical optional non-claim alternative. Bounded temporary words are required; compressed additional temporary bits are not.

## O-REPR

Exact old plan row (C.2):

```text
| O-REPR | **Signed-word representability** of every input and compared operand at the declared width, with a comparison/order refinement theorem and an exhibited satisfiable all-size family. **Absent this, public wording says "unit-cost comparison oracle"** | — | accepted `P1-7` |
```

Replacement: Separate arbitrary-Int unit-cost comparison-oracle and finite-key word-machine corollaries. The latter proves pointwise signed representation, order refinement, every operand bound and satisfiable all-size guards.

Rationale and consequence: This strengthens the historical wording choice into two mandatory propositions. Input reads/comparisons/materialization are explicit; no free sorting or rank conversion.

## O-COUNT

Exact old plan row (C.2):

```text
| O-COUNT | Report **five wrappers / eight encoded tables**; no `2n` forecast until DD-E | — | accepted `P2-3` |
```

Replacement: Preserve exact five interior wrappers/eight encoded tables and all outer payload components, metadata and padding. Retained 2n+o(n) follows from the existing PQ1 capacity theorem only through exact emitted allocation equality.

Rationale and consequence: PQ1 acceptance supplies the retained-space theorem that was previously pending DD-E. It does not supply preprocessing work or workspace bounds.

## O-NOINHERIT

Exact old plan row (C.2):

```text
| O-NOINHERIT | **No inheritance** — `REQ-BLD-06`'s third conjunct, named explicitly rather than inherited, on the same principle `O-FIREWALL` is named | — | `R11 [BOTH]` |
```

Replacement: All non-input memory initially absent outside the declared extent; all registers zero; CleanTail preserved; initialized/output cells arise only from charged stores.

Rationale and consequence: The exact old REQ-BLD-06 surface is replaced by numeric mutable storage. No metadata, rank conversions or semantic answers may be preseeded.

## O-REPLAY

Exact old plan row (C.2):

```text
| O-REPLAY | **Replay is not the anti-oracle** — stated as a non-goal. Kills nothing on its own: `R11` says replay is "necessary, nearly free, and insufficient", and locates the anti-oracle content in program uniformity (`O-UNIF`), the interpreter firewall (`O-FIREWALL`), **the reflected work cap (`O-WORKCAP`)**, no-inheritance (`REQ-BLD-06`'s third conjunct, `O-NOINHERIT`) **and the pointwise input encoding (`REQ-BLD-08`, `O-POINTWISE`)**. | — | `R11 [BOTH]` |
```

Replacement: Replay is necessary and insufficient. Reflected execution, uniformity, input locality, no-inheritance and firewall are separate load-bearing obligations.

Rationale and consequence: The non-goal is preserved. A correct result or replay equation alone cannot reject the canonical oracle.

## R1, R2, R12 and R13 exact source repair clauses

These source clauses distinguish the closed-program alternative from the eventual size-indexed information gap, and pin the mandatory audit order.

```text
R1 [B, FATAL — kills FK-5]. Replace REQ-BLD-09 with A's O1 verbatim: `builderProgram : Program` is a single closed constant with no parameters and `builderProgram.length = <literal>` by `rfl`; the input length arrives in a register, read from a pinned header cell of the input segment (add `(encodeInput xs).readWord? inputSegment 0 = some (encodeInt wordBits xs.length)` to REQ-BLD-08 and shift the element cells by one). If a size-indexed family is kept instead, the row is NOT optional and must read: `theorem builderProgram_information_gap : ∀ n, n₀ ≤ n → ∀ shape ∈ Cartesian.shapesOfSize n, (builderProgram n).length * instrBits < (concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape).length`, with `instrBits := tagBits + maxFieldCount * wordBits` and `n₀` a literal. Without one of these two forms, a per-size decision tree emitting literal payload constants satisfies all sixteen of B's rows.
```

```text
R2 [A AND B, FATAL — kills FK-3, and gives A's O14 its only teeth]. REFLECTED ISA WITH A LITERAL PER-INSTRUCTION WORK CAP. The interpreter must be data, not a Lean function: `inductive Prim | constZero | succ | add | sub | mulConst (c : Nat) | divConst (c : Nat) | lt | le | eq | getBit | setBit`; `def Prim.constants : Prim → List Nat` (constructor-exhaustive, no wildcard); `def BInstr.semantics : BInstr → List Prim` (constructor-exhaustive, no wildcard); and THREE theorems, of which the first is the one that stops `semantics` from being a decoration: `theorem bstep_reflects : ∀ i s, bstep i s = interpretPrims i.semantics s`; `theorem semantics_cap : ∀ i : BInstr, (i.semantics).length ≤ primCap` with `primCap` a literal; `theorem prim_const_cap : ∀ i : BInstr, ∀ p ∈ i.semantics, ∀ c ∈ p.constants, c < 2 ^ wordBits`. Note explicitly in the row that `Prim` must contain NO table-lookup constructor and no constructor with an unbounded `Nat` payload, and that adding one must break `Prim.constants`'s wildcard-free match at compile time (precedent: `Instr.FieldsFit` design note, RMQ/Core/WordRAM/E1Machine.lean:492-497). With R2 in place, A's `unchargedStepBound` is replaced by the computed `(i.semantics).length` and R1's bit budget can be extended to `isaBits + progBits < payloadBits`, closing the static-information argument over the interpreter as well as the program.
```

```text
R12 [BOTH]. Add a negative control that a CURRENT-repo-shaped oracle FAILS, as a checked theorem rather than a placeholder. Concretely: exhibit a hypothetical instruction `oracleWord (dst src : Nat)` and prove `¬ ∃ ps : List Prim, ps.length ≤ primCap ∧ interpretPrims ps = oracleSemantics` (R2), AND exhibit a `builderProgram` variant with a baked constant table and prove it violates R1's information gap. A's O13_oracle_rejected is currently the prose placeholder `<p writes the payload with no input read>` and is not a proposition; B's REQ-BLD-14 has (a) (b) (c) but no oracle-rejection row at all.
```

```text
R13 [PROCESS, BOTH]. Freeze order matters and neither contract states it: R1, R2, R5 and R12 are the rows on which every other row's meaning depends, and all four are cheap. They must be landed and blind-audited BEFORE any builder construction work begins, so that a later worker cannot discharge O9/REQ-BLD-07 honestly against a machine whose ISA has already been widened. This is the same failure geometry as A's own O3 warning ('the only obligation whose failure mode is silent') applied to the contract as a whole.
```

## Task-specific authorization and strengthened endpoint

The historical old-machine freeze and extraction/C-Rust non-goals are not an authority to reject this explicitly authorized extension. PRE-1 adds an isolated mutable primitive model and an efficient builder after contract acceptance; it does not edit the old query machine or implement the separate compiler lane. The historical fallback provenance-only claim and optional unbounded scratch exclusion cannot replace the new linear-work/temporary-word target. No historical requirement or coverage table was edited.

## Version 2 entries (2026-09-12, after fresh blind audit PRE-1-A1)

Version 2, appended after the fresh blind exact-commit contract audit PRE-1-A1 on `c1c970b8bfbae03163633365e512d487ae1c98f2` (verdict CONTRACT_AUDIT_PASS_WITH_REQUIRED_AMENDMENTS; report `docs/internal/audit_reports/2026-09-12_PRE1_contract_fresh_blind.md`) and the coordinator's binding rulings. Nothing in the version-1 ledger above is edited. Where a version-2 entry supersedes a version-1 replacement sentence, that sentence is quoted byte-exact and the version-2 wording governs. The corresponding contract clauses are CONTRACT.md V2-1 to V2-8.

### O-POINTWISE header clause, version 2

Exact version-1 replacement sentence superseded:

```text
Zero initial registers must obtain the header through the actual load; missing header faults for all lengths.
```

Version 2 replacement: Zero initial registers; the accepted run must obtain the input length through the actual header load, as a checked certificate field named `HeaderUse` on the actual accepted run, for both input models and every xs including []. `HeaderUse` is the conjunction of (a) `buildProgram[0]? = some headerInstruction` (rfl) and `buildProgramWord[0]? = some headerInstruction`, read with the O-UNIF version-2 declaration names `builderProgram`/`builderProgramWord`; (b) `WritesOnly (fun r => r != 1)` on the program tail, checked by decide, so register 1 is written only by the header load; (c) the run from the header-removed initial state (`{ wordInputState width xs with memory := put (encodeInput width xs) 0 none }` and `{ comparisonInputState xs with memory := put _ 0 none }`) has status fault with steps = 1, writes = [], reserves = [] and unchanged extent for every fuel >= 1; (d) the first transition of the intact run is the header load taking register 1 from 0 to xs.length; (e) the structural fact `(comparisonInputState xs).extent = 1`. Every conjunct is projected by the typed consumer, and the builder replay registry has a case deleting or weakening each conjunct.

Rationale and consequence: reserve exposes extent = n + 1 in the word model, so a program can recover n without any load (audit finding P1-1, demonstrated by a compiled probe); the version-1 sentence constrained the single header instruction, not the accepted program's run. The unsigned-header/biased-key encoding split of version 1 is unchanged.

### O-UNIF, version 2

Version-1 replacement sentence refined (not deleted):

```text
One closed finite program for all xs, including empty input; exact literal instruction and encoded-word counts; all code words counted at the declared width.
```

Version 2 replacement: Exactly one closed, parameterless, literal-pinned Program constant per input model, both compiled from one shared source template `builderSource` and differing only in the key-comparison leaf: `builderProgram` (comparison-oracle model; leaf loadKey/loadKey/compareKey padded with two move no-ops; the primary C1 constant and the REQ-PRE-EXACT/REQ-PRE-COST witness) and `builderProgramWord` (finite-key word model; leaf add/load/add/load/comparison .lt; the REQ-PRE-INPUT finite-key corollary constant under `InputFits (wordWidth xs.length) xs`). Each has its own ProgramContract instance with family definitionally `fun _ => <constant>`, its own instruction-count and encoded-word literal pins proved by rfl on the compiled list, and there is a rfl theorem that the two constants have equal length and differ exactly at the literal leaf positions. Correction: ProgramContract fixes instruction count and encoded-word count to Nat parameters; the typed consumer pins the numerals. Builder replay cases must (i) parametrize a constant by width or size and (ii) change each literal numeral, each failing at a pinned consumer line.

Rationale and consequence: audit finding P1-2 (family is a free parameter, the pins are Nat parameters, so a width-indexed family could be certified per member; width-indexing is size-indexing because wordWidth is a function of n) and coordinator ruling Q1. Size/shape-dependent families still fail the actual Uniform predicate; the parameterless-constant rule closes the width route.

### O-FIREWALL, version 2

Exact version-1 replacement sentence superseded:

```text
Future program/run modules require an explicit reviewed closure extension.
```

Version 2 replacement: The contract guard `scripts/preprocessing_contract_firewall.ps1` and `primitive_manifest.json` stay byte-identical (their surfaces are frozen by contract registry cases C17/C18). Future program/run modules enter through a LAYERED builder guard `scripts/preprocessing_builder_firewall.ps1` with `builder_manifest.json` version 1, which first requires the contract guard's PASS, then checks the exact allowed-imports table and the full transitive import closure of the operational modules (Program, Calculus, Safety, Structured, Compiler, Loop, ArrayRun, Builder/*) against {Std, Primitive, Input, Model, earlier closure modules} and their strict-UTF-8 CRLF-to-LF normalized hashes. Two scripts/gate.ps1 checkers, `PRE1-CONTRACT-GATE` (contract firewall, then `lake build RMQ.Core.WordRAM.Construction.Contract`, then `lake env lean scripts/preprocessing_contract_check.lean`) and `PRE1-BUILDER-REPLAY` (`scripts/preprocessing_builder_replay.ps1` in full with its own measured deadline at >= 2x margin), raise the roster from 18 to 20 with GATE COVERAGE 20 of 20, so the historical "CI-enforced" property holds again.

Rationale and consequence: audit finding P2-1 (no gate or CI reached the firewall, the contract build or the typed consumer; the aggregate PASS was silent about the Construction modules) and coordinator ruling Q4. The tighter closure of version 1 is kept; only its enforcement reach changes.

### O-BITS / O-WRITE, version 2

Version 2 addition to O-BITS (AMEND-3, audit finding P1-3): `efficientBuild xs` is defined inside the firewalled closure as the positional projection `emitted final outBase len` of the accepted run's final memory, with outBase the halt value and len = extent - outBase, never through a function naming buildMemory, cartesianShape, metadata or any semantic builder, and never through an intermediate adapter store; `efficientBuildWord` likewise; the equality theorems have this syntactic left-hand side.

Version 2 addition to O-WRITE: the work unit is one interpreter transition through checkedStep; executed work is the transition count partitioned over the ten Prim.category values (read, register, arithmetic, comparison, branch, control, write, allocation, keyRead, oracleComparison), with reserve, store, loadKey, compareKey and padding moves each one unit. Ordered words and positional address/value provenance remain required as in version 1.

Rationale and consequence: exact equality to buildMemory xs is meaningful only for the list the run actually wrote, and the cost theorem is meaningful only for transitions of the frozen interpreter.

### O-SCRATCH, version 2

Version 2 addition: The bit-per-cell temporary buffer (one numeric cell per emitted bit, Horner-packed into the output words) is accepted O(n)-word temporary workspace. The workspace account separates input (n+1 numeric cells in the word model; 1 numeric cell plus n key-bank cells in the comparison model; materialization outside the builder boundary with zero builder input writes; the retained input is never stored to), code (programWords at the declared width, joined with the PQ1 query code account), temporary (peak live extent beyond input and output, <= Cw*n + Dw words), output ((buildMemory xs).length words) and the historical peak extent including the output region, reported beside the temporary bound.

Rationale and consequence: coordinator acceptance of the route study's workspace entries; compressed temporary bits remain not required, and the version-1 bound is unchanged in form.

### Audit recommendations adopted

R1: a single per-transition safety judgment `Prim.Safe width s p` (operand fit, arithmetic result < 2^width, sub non-underflow, positive div/mod divisor, shl/shr operand < width, store/load address < extent with present cell and value < 2^width, loadKey present key, reserve extent+1 < 2^width, branch/jump targets < program length, no jumpRegister), with `Run.Safe` as every transition safe with a fitting post-state and fault-freedom part of Safe; the Safety.lean module of Stage 0 and the only safety vocabulary of later stages (CONTRACT.md V2-6).

R2: the builder replay verdict matcher requires the set of failing consumer lines to equal the expected set, not merely to contain it.

R3: Program, Uniform, programWords and CodeAccounting stay in Controls.lean and are consumed only from outside the closure; the firewalled modules operate on List BInstr literally (CONTRACT.md V2-5).

R4: ATTACK_TABLE.md is corrected by version-2 rows: FK-1's rejecting basis is run identity (REQ-PRE-EXACT/REQ-PRE-MACHINE, INV-TRACE-EXECUTION, INV-NO-SYNTHETIC), not O-REPLAY; FK-5's cheap variant (fixed shape-independent tables inside the one fixed program) is counted code, not forbidden.

## Version 3 entries (2026-09-13, after continuation audit PRE-1-A1C)

Version 3, appended after the continuation audit PRE-1-A1C on `5f325ddb856b9095d1ad2aacc0bc69eda571d447` (verdict CONTINUATION_PASS_WITH_CONDITIONS; report `2026-09-13_PRE1_contract_continuation.md`, SHA-256 2650BA3CC8CF8DDEB58E53DDC45121DFB127E0728B957A2FD540AD8B779B6A0A) and the coordinator's acceptance of conditions C1-C3. Text only; nothing in the version-1 or version-2 ledger above is edited. The corresponding contract clauses are CONTRACT.md V3-1 to V3-10, which govern where they refine version 2.

### O-UNIF, version 3

Version 3 addition (condition C1(a)-(e), (g)): the template, body, both leaves, both constants, the fuel function and both extraction functions are declared in `RMQ/Core/WordRAM/Construction/Builder/Program.lean`, namespace `RMQ.SuccinctFinal.PackedConstruction`, a builder-firewall table key with a manifest hash, with a consumer `run_cmd` location check and a registered relocation case (V3-1); the consumer carries `example : List BInstr := @builderProgram` and `@builderProgramWord` (V3-2); `builderProgram = (builderSource keyLeaf).compileAt 0 ++ [⟨.halt 3⟩]` and `builderProgramWord = (builderSource wordLeaf).compileAt 0 ++ [⟨.halt 3⟩]` by `rfl`, with `keyLeaf` = loadKey 0 4; loadKey 1 5; compareKey 6 0 1; move 6 6; move 6 6 and `wordLeaf` = add 7 4 2; load 7 7; add 8 5 2; load 8 8; comparison lt 6 7 8 as right-nested five-action sequences by `rfl` (V3-3); a leaf-difference theorem pinning the differing positions and the literal instruction of each constant at each of them (V3-4); both `ProgramContract` instances restated with decimal numerals `L`, `B`, `B'` (V3-5); replay cases (i) optional-parameter mutations of each constant through the C3 per-mutation manifest re-hash, rejected at exactly the corresponding `@` line, and (ii) one consumer-numeral mutation per numeral, each rejected at its exact line set (V3-7).

Rationale and consequence: audit finding P2-1 scenarios (1), (2), (4), (5); the future surfaces become mechanically rejectable instead of arguable. Naming follows V2-2 (coordinator resolution of audit P3-3); BUILDER_PLAN.md usages are renamed in the same commit.

### O-BITS / O-WRITE, version 3

Version 3 addition (condition C1(f)): `efficientBuild xs` matches on the final status of `run builderProgram (builderBudget xs.length) (comparisonInputState xs)`, returning `emitted final outBase (final.extent - outBase)` for `.halted outBase` and `[]` otherwise; `efficientBuildWord width xs` is the same over `builderProgramWord` and `wordInputState width xs`; both bodies are pinned by `rfl` in the consumer, the word pin at `width := wordWidth xs.length`; the equality theorems are `efficientBuild_eq_buildMemory : ∀ xs, efficientBuild xs = buildMemory xs` and `efficientBuildWord_eq_buildMemory : ∀ xs, InputFits (wordWidth xs.length) xs → efficientBuildWord (wordWidth xs.length) xs = buildMemory xs`; `builderBudget n = C * n + D` with numerals pinned at S8 (V3-6). The explicit width argument is required because `wordWidth` lies outside the builder firewall; the program constant stays parameterless.

Rationale and consequence: audit finding P2-1 scenario (3) and P3-4; the non-halting branch can no longer project cells from address 0, and the plan's `r.result.getD 0` sketch is superseded.

### O-POINTWISE header clause, version 3

Version 3 qualification (condition C1(h), audit finding P2-2), recorded as a limit: in the word model `HeaderUse` certifies the header load, the register-1 frame and the missing-header fault, not that the output depends on the loaded header value, because `reserve` exposes the extent `n + 1`; in the comparison-oracle model the only length source is cell 0, so exactness of the primary witness forces header use. No value-dependence theorem is required (V3-8).

Version 3 refinement (condition C1(i)): `tailNeverWritesR1` at both constants is discharged by `Structured.Block.compile_writesOnly` from `(builderBody leaf).WritesOnly (· ≠ 1)`, proved compositionally by structural simplification, plus the destination-free final halt; no kernel `decide` over the whole compiled list or template (V3-9), superseding version 2's "checked by decide".

### Conditions C2 and C3 accepted by the coordinator

C2: `B14_HEADERFIRST_CONSUMER` (surface `preprocessing_builder_check.lean:20:`) before S7 instantiates `HeaderUse` at the constants. C3: a per-mutation manifest re-hash and V3-7 case (i) before S7 registers the constants' cases; consumer-reaching foundation cases before the S8 candidate is frozen; with it, an own deadline for the nested contract guard (audit P3-7) and PASS markers printed only after successful elaboration (audit P3-1). Ruling Q9a stands (V3-10).

### O-BITS / O-WRITE, version 3 amendment V3-6a (2026-09-13, coordinator ruling R-S7-5)

Version 3 amendment, appended after the S7 checkpoint `5dff46edf0d4d7a01a775afeddb8a3259249e9d4` reported the fuel-body obstruction and the coordinator ruled (record `PRE1_S7_V36_RULING.md`, 4,240 bytes, SHA-256 B355736C0B77E805148E0169390AF20E2B12A7EDB47E797B5CA106D2648800A0). Text only; nothing above is edited. It supersedes the phrase "`builderBudget n = C * n + D` with numerals pinned at S8 (V3-6)" of the O-BITS / O-WRITE version 3 entry: the fuel body is `builderBudget n = D + C * n` with decimal numerals pinned by `rfl` at S8, with `builderBudget_eq_mul_add : ∀ n, builderBudget n = C * n + D` proved propositionally and restated at full type in the stage consumer; crude literals remain acceptable, fuel sufficiency is proved for every `n` from the stage cost theorems, and no other fuel-body variant is admitted. All other version 3 requirements stand, including the `rfl` pins of both extraction bodies. Reason and reproduction tables: CONTRACT.md V3-6, amendment V3-6a (a trailing fuel literal is peeled one successor at a time by kernel reduction of the extraction match; BUILDER_STAGE_LOG.md S7-14..S7-16 and the coordinator's `pre1-v36-repro/`).

## Version 3 entries, repair PRE-1-R2 (2026-09-14, after fresh blind audit PRE-1-A2)

Appended after the fresh blind audit PRE-1-A2 of `84ae12f6f6bad99fd3215c5bdd5b2a93e3779897` (report `2026-09-14_PRE1_builder_fresh_blind.md`, 53,979 bytes, SHA-256 bda5f41450dddaf4cec8fc898e63d99881a12fece96f4ccc476b3fa2f82ed180) and the coordinator's repair prompt `PRE1_R2_CONSUMER_MARKERS.md` (18,929 bytes, SHA-256 60499BD23101670392C011EA08B4D4B78C23FF9B6B629C655940CD43C9267C2B). Text only; nothing above is edited. The corresponding contract clauses are CONTRACT.md V3-7a and V3-10a at the end of its Version 3 section.

### O-UNIF, version 3 amendment V3-7a (2026-09-14, PRE-1-A2 P3-1)

It supersedes, for `Cw` and `Dw` only, the V3-7 (ii) text "One registry mutation per consumer numeral: `L`, `B`, `B'`, each element of `P` in V3-4 and, at S8, `C`, `D`, `Cw` and `Dw`. Each changes that numeral in `scripts/preprocessing_builder_check.lean` only and is rejected at the consumer with the exact failing line set of the theorem stating it." The `Cw` and `Dw` numeral cases are consumer cases in `RMQ/Validation/PreprocessingContract.lean` rather than `scripts/preprocessing_builder_check.lean`: `B50_CAPSTONE_CW_NUMERAL` and `B51_CAPSTONE_DW_NUMERAL` change the numeral in `check_comparisonRun_workspace` (capstone profile) and are rejected at `PreprocessingContract.lean:275:`. The other numeral cases stand as written.

Rationale and consequence: `Cw` and `Dw` belong to `BuilderRunFacts.workspace`, exported only through `ConstructionAndQueryCapstone`, whose exact-type consumer is the capstone consumer; stating them in the builder consumer would import the stage proof tower into every closure-module case (DD-20260913-PRE1-017, DD-20260913-PRE1-018). The audit found the placement unrecorded (P3-1); this entry records it.

### Condition C3 marker clause, version 3 amendment V3-10a (2026-09-14, PRE-1-A2 P2-1)

It refines the V3-10 (C3) clause "both typed consumers print their PASS marker only after successful elaboration": the builder, capstone, contract, spec and stage typed consumers print their markers if and only if the whole file elaborated with no error-severity message and their existing witness and guard conditions hold. The contract consumer's verdict-marker command is changed accordingly (this is the contract amendment entry for that change); no contract registry line, runner, firewall or manifest changes. The builder replay registry version 2 also requires a consumer-stage rejection to lack the profile's marker.

Rationale and consequence: on `a0c93e9cf4d3c93856f5756ff6a7271da2b821ff` every consumer printed its marker on failing runs (B16-B18; CAB2 and CAB4 maximum-recursion-depth failures; injected failing examples, `#guard` checks, unreferenced declarations and trailing commands), because the marker read only the witness's axioms and Lean 4.22.0 resets the command message log before each command. The marker command now re-elaborates the file's own text in-process with itself blanked and reads every command's message log (`repair-r2/marker_controls.json`, `repair-r2/run_marker_controls.ps1`).
