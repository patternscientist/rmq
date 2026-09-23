# PRE-1 current construction contract, version 1

Status: contract authoring for mandatory independent audit. This document
does not authorize construction before the coordinator returns a passing
exact-commit contract audit. The source/governance baseline is
`0e6a00f654abc64f8b68988fa9675b9a839dca2f`.

## Target and phase boundary

The assigned join is one uniform efficient builder of the **exact ordered
numeric list** `RMQ.SuccinctFinal.PackedWordRAM.buildMemory xs`, followed by
the existing accepted packed query on those emitted cells. The eventual
declarations remain `PackedConstruction.efficientBuild_eq_buildMemory` and
`PackedConstruction.constructionAndQueryCapstone_holds`, with the capstone in
`RMQ/Core/WordRAM/Construction/Capstone.lean`. None is claimed in this phase.

This phase establishes the interpretation and input prerequisites, states the
program schema, checks oracle and certificate controls, and supplies the
15-case author table. The actual program and its literal length/encoding pins
are construction-phase producers. A universally quantified schema is not a
claim that a program builds the allocation. In particular an empty or constant
program satisfying the uniformity schema cannot satisfy the later exactness,
halting and output obligations.

## C1 / O-UNIF and O-POINTWISE

The production program must be one closed finite `Program` constant. Every
`xs : List Int`, at every length including zero, uses that same constant;
`Uniform program family` is exactly `forall xs, family xs = program`.
`ProgramContract` additionally fixes instruction count and full encoded-word
count to source-level literal numerals. Before claiming the builder, direct
typed consumers must pin those exact numerals and the unparameterized program
declaration; deriving a free bound from the resulting code does not discharge
the literal-pin requirement. The contract-phase theorem provides prerequisites,
not a fictitious builder program or a claimed final code length.

`programWords` counts opcode tags, arithmetic/comparison sub-tags, immediates,
register identifiers and control-flow targets. At word width W, code occupies
`programWords program * W` bits. Interpreter operations form a fixed finite
instruction set; their semantics and all encoded literals are audited and
frozen, not a per-input Lean function. Any input-dependent tables or constants
must be generated as charged data and included in live storage. A fixed finite
constant table is code/data that must be counted; uniformity does not pretend
that a finite table is impossible. An unbounded size/shape-dependent baked
family is rejected by exactly the same `Uniform` predicate.

The obsolete all-size strict information gap is replaced as documented in
AMENDMENTS.md. Fixed code has an explicit all-size additive storage account.
Only an eventual asymptotic absorption may place it in the residual term;
the construction capstone must join its own code account with the existing
PQ1 query program's code account. There is no claim that code is smaller than
the payload at n=0 or below a fixed threshold.

There are two stated input models. In the arbitrary-Int comparison-oracle
model, the supplied input consists of n key cells and one unsigned numeric
header; each key-cell read and comparison is a distinct charged primitive.
Keys cannot be converted to numeric answers except through loaded-key
comparisons. Neither sorting nor rank conversion is free. In the finite-key
word model, cell 0 contains the unsigned length n and cell i+1 contains the
biased signed encoding of xs[i]. A fixed width and representability hypotheses
make this encoding injective and order-preserving. No cell can carry the
Cartesian shape or another key's data.

Both models start with zero registers, and the length is obtained by the
actual `headerInstruction = load 1 0`. Missing cell 0 faults, including for
n=0. The header is not supplied independently in a register. Pointwise input
materialization is an explicit input-cost obligation: n+1 supplied cells,
with n+1 input writes/initializations if materialization is included in the
builder boundary. The pure `encodeInput` function is only a specification of
supplied storage; it is not an uncharged stage of the production program.

`InputFits` states only signed key and unsigned header representability. The
machine/capstone must separately establish the capacity of n+1, all temporary
addresses and sentinels. `inputFits_all_sizes` is a simple n+2-width input
witness, not the required logarithmic-width capstone. `zero_inputFits`
provides the conditional all-size zero family at any positive width whose
header fits; the final proof must instantiate the actual common width.

## C2 / O-WORKCAP

Primitive.lean is the operational root and imports only Std. Its finite
`Prim` data has the old word instruction categories plus single-word store,
single-cell reserve, input-key read and loaded-key comparison. Every encoded
operand has type `Fin (2^32)`, including dormant targets, registers and tags.
`constants_fit_width` embeds that bound into any declared width W>=32. The
eventual construction must fit all live values and dynamic addresses at a
single logarithmic width; operand syntax alone does not prove this.

The new syntax does not expose a callback, table lookup or semantic builder.
`BInstr` contains one primitive, `semantics` reflects its singleton sequence,
and `bstep_reflects` equates the actual scalar evaluator to that sequence.
`semantics_cap` pins the primitive cap to literal 1. The operational evaluator
has no host-list scan, recursive RMQ call, or uncharged variable-length helper.
Arithmetic operations follow the existing PQ1 model, including multiplication,
division, remainder, shifts and bitwise operations; later safety proves no
overflow, underflow, zero division or oversized shift on accepted runs.

Reservation increases the live numeric extent by one and returns the address.
It does not initialize that cell. `CleanTail` excludes preseeded values outside
the extent; preservation plus `reserve_fresh` supplies an absent cell. A later
store initializes it, with a separate write charge. No instruction allocates,
initializes, copies or releases an arbitrary-size block in one tick. The
construction can reuse owned temporary regions; it must account for its peak
live extent and retained input. Final detachment of the output does not erase
the historical peak from the workspace theorem.

The full interpreter must fetch from the fixed program and use `checkedStep`
to stop at fault/halt. Each actual primitive transition contributes one work
unit; category counts partition those transitions. Loop branches, input and
numeric reads, stores, reserve/initialization, arithmetic, comparisons and
control transitions all count. The construction proof must derive work from
that interpreter, not attach a counter to a semantic builder. Program fetch,
fixed register ports and PC progression use the same instruction convention
as PQ1; charged program storage and finite address/operand bounds remain
explicit. Functional indexed stores are mathematical RAM states, not a claim
about Lean's functional-update runtime cost. Reflected sequence recursion is
over charged instructions, not over a host-list memory representation.

Conservative.lean is a separate semantic bridge to the accepted old primitive
model. Old instructions fit the new finite operand syntax under their 32-bit
field premise. The bridge must preserve numeric registers, PC/status, memory
and the unchanged key banks for running prestates. It does not edit PQ1 or
prove a builder execution.

## C3 / O-FIREWALL

The production firewall checks the exact repository import closure:

| Root | Allowed direct imports |
| --- | --- |
| Primitive.lean | Std |
| Input.lean | Std |
| Model.lean | Construction.Primitive, Construction.Input |

The input encoder and initial states are supplied-storage specifications,
outside the primitive evaluator. Controls.lean, Conservative.lean and
Contract.lean are consumers outside this operational closure. In particular
the deliberately forbidden oracle in Controls.lean can never become an
interpreter dependency. Future Program/Run files must extend the explicit
firewall only with reviewed primitive-only modules, before builder acceptance.

`preprocessing_contract_firewall.ps1` checks imports and normalized UTF-8 source
hashes from the exact primitive manifest. Import checks reject direct semantic
access; frozen evaluator bytes prevent a copied semantic implementation from
quietly entering an audited arm. This manifest is a review/change-control
boundary, not a formal proof that arbitrary Lean source is primitive. Atomicity
also requires inspecting each enumerated evaluator arm and the checked
reflection/cap statements. The replay invokes this production guard before
compilation, without weakening the repository aggregate gate.

## C4 / O-CONTROL

`oracleSemantics` computes the existing `Cartesian.stackCartesianShape` BP
serialization of two key cells and places its little-endian code in numeric
register 0. It is a current-reference-shaped forbidden macro, implemented only
in the negative-control module. Increasing/equal inputs produce 5; decreasing
input produces 3, preserving the existing leftmost tie policy.

`oracle_not_reflected` rejects exactly
`exists ps, ps.length <= primCap and forall s, interpretPrims ps s = oracleSemantics s`.
Its proof uses numeric-result independence from the key-input store for every
zero/one-primitive sequence and two legitimate same-length inputs. A key read
alone only changes a key register; a comparison alone sees old loaded keys.
The contradiction is in the numeric returned-register projection, not a log.
This is a canonical BP-word exhibit, not an assertion about an evaluated full
PQ1 physical cell; the complete emitted-allocation controls remain required
with the builder. Arbitrary-Int and finite-key guards remain explicit.

`baked_not_uniform` rejects the same-length, shape-dependent constant-emission family at the
same `Uniform` predicate used by `ProgramContract`. `Replays` is a plain-data
write-fold equality and hosts a fabricated-result rejection, but replay is
not sufficient anti-oracle evidence. The semantic oracle can produce a correct
answer, so exactness alone is also insufficient.

Every `ContractPrerequisites` field is projected by an independently typed
consumer in scripts/preprocessing_contract_check.lean. The committed registry
mutates actual producer declarations, including deletion, weakening and sibling
substitution, and has an expected-accept comment change. Producer compilation
must precede the consumer to prevent stale interface artifacts from passing.
This certificate certifies prerequisites only; the eventual public capstone
must independently pin its own complete fields, objects and guards.

## Required construction after contract acceptance

The complete pipeline must implement a monotone stack with strict pops,
linear-order BP emission, one-pass rank/select construction, all interior
wrappers/tables, microtable generation, all metadata fields, both padding
layers and dense repacking. Exact equality fixes order and content; a free
padding term or only matching lengths cannot replace it. SOURCE_FACTS.md
identifies each current reference definition and its repeated-scan trap.

The full capstone must quantify the same xs, program, input store, emitted
cells, common word width, builder execution and following PQ1 query. It must
prove explicit literal linear work and peak temporary-word constants for all
sizes, plus word/address safety, positional read/write provenance, actual
execution traces, supplied-store agreement, complete ownership and input/code/
temporary/output separation. It must transport the existing retained-space,
reference answer, invalid-range and fully charged query facts through exact
emitted allocation equality. Arbitrary-Int comparison-oracle and finite-key
word-machine corollaries are separate statements. All corresponding frozen
REQ/INV rows stay open until these producers and consumers exist and pass audit.

## Review and gate order

Author checks, the 15-case table and a frozen contract commit precede the
coordinator-scheduled aggregate gate. The plan's gate is scripts/gate.ps1;
focused contract checks supplement it because the existing default root does
not import these new declarations. A fresh blind exact-commit contract audit
then precedes builder implementation. No author theorem, registry PASS or
resource wait replaces that audit. Final roadmap and public synchronization
remain coordinator responsibilities.

## Version 2 amendments (2026-09-12, after fresh blind audit PRE-1-A1)

Status: append-only version-2 entries. They record the amendments made
binding by the fresh blind exact-commit contract audit PRE-1-A1 (verdict
CONTRACT_AUDIT_PASS_WITH_REQUIRED_AMENDMENTS on
`c1c970b8bfbae03163633365e512d487ae1c98f2`; report
`docs/internal/audit_reports/2026-09-12_PRE1_contract_fresh_blind.md`) and
the coordinator's binding rulings. Nothing in the version-1 body above has
been edited. Each subsection quotes, byte-exact and in a fenced block, any
version-1 sentence it supersedes, then states the version-2 text, then the
rationale with the audit finding it answers. Module names follow the
coordinator's builder plan (`docs/internal/extensions/pre1/BUILDER_PLAN.md`):
the operational modules
`RMQ/Core/WordRAM/Construction/{Program,Calculus,Safety,Structured,Compiler,Loop,ArrayRun}.lean`
and `Builder/*.lean` live inside the builder firewall; consumers live outside
it.

### V2-1 C1 header clause: the accepted run must read the header (AMEND-1, finding P1-1)

Supersedes (CONTRACT.md version 1, lines 64-66):

```text
Both models start with zero registers, and the length is obtained by the
actual `headerInstruction = load 1 0`. Missing cell 0 faults, including for
n=0. The header is not supplied independently in a register.
```

Version 2: Both models start with zero registers. The accepted run must
obtain the input length through the actual header load, and this is a
checked certificate field named `HeaderUse`, stated on the actual accepted
run, for both input models and every `xs` including `[]`. `HeaderUse` is the
conjunction of:

- (a) `buildProgram[0]? = some headerInstruction` (by `rfl`) and
  `buildProgramWord[0]? = some headerInstruction`;
- (b) `WritesOnly (fun r => r != 1)` on the program tail, checked by
  `decide`, so register 1 is written only by the header load;
- (c) the run from the header-removed initial state
  (`{ wordInputState width xs with memory := put (encodeInput width xs) 0 none }`
  and `{ comparisonInputState xs with memory := put _ 0 none }`) has status
  fault with steps = 1, writes = [], reserves = [] and unchanged extent, for
  every fuel >= 1;
- (d) the first transition of the intact run is the header load, taking
  register 1 from 0 to `xs.length`;
- (e) the structural fact `(comparisonInputState xs).extent = 1`.

Naming: AMEND-1 writes the two constants as `buildProgram` and
`buildProgramWord`; V2-2 below fixes their declaration names as
`builderProgram` (comparison-oracle model) and `builderProgramWord` (word
model). Conjunct (a) is read with the V2-2 names; the typed consumer pins the
actual declarations.

Every conjunct is projected by the typed consumer at its full type, and the
builder replay registry carries a case deleting or weakening each conjunct,
failing at a pinned consumer line.

Rationale: finding P1-1 (HEADER-AND-LENGTH-LEAK). `reserve` exposes
`extent = n + 1` in the word model, so the audit's compiled probe
`[reserve 2, constant 3 1, arithmetic sub 1 2 3]` recovers `n` in register 1
without any load, inhabits `ProgramContract` at literal pins and keeps
running when cell 0 is absent; the version-1 clause was prose only, and no
field, consumer line or guard rejected the probe. The missing-header control
is meaningful only if the run itself must read the header.

### V2-2 C1 program constants: one closed constant per input model, both from one template (AMEND-2, finding P1-2, ruling Q1)

Supersedes (CONTRACT.md version 1, lines 27-28):

```text
The production program must be one closed finite `Program` constant. Every
`xs : List Int`, at every length including zero, uses that same constant;
```

Version 2: The production program is exactly one closed, parameterless,
literal-pinned `Program` constant per input model, both compiled from ONE
shared source template `builderSource` and differing only in the
key-comparison leaf. `builderProgram` (comparison-oracle model; leaf
`loadKey`/`loadKey`/`compareKey` padded with two `move` no-ops) is THE
primary C1 constant and the REQ-PRE-EXACT/REQ-PRE-COST witness.
`builderProgramWord` (finite-key word model; leaf
`add`/`load`/`add`/`load`/`comparison .lt`) is the REQ-PRE-INPUT finite-key
corollary constant under `InputFits (wordWidth xs.length) xs`. Every
`xs : List Int`, at every length including zero, uses the constant of its
input model. Each constant has its own `ProgramContract` instance with
`family` definitionally `fun _ => <constant>`, its own instruction-count and
encoded-word literal pins proved by `rfl` on the compiled list (the
`QueryStatic.lean` pattern), and there is a `rfl` theorem that the two
constants have equal length and differ exactly at the literal leaf
positions. Neither constant takes a width, size or input parameter.

Also supersedes (CONTRACT.md version 1, lines 30-31):

```text
`ProgramContract` additionally fixes instruction count and full encoded-word
count to source-level literal numerals.
```

Version 2: `ProgramContract` fixes instruction count and full encoded-word
count to `Nat` parameters; the typed consumer pins those parameters to
source-level literal numerals. The rest of the version-1 paragraph (direct
typed consumers must pin the exact numerals and the unparameterized
declaration; deriving a free bound does not discharge the pin) stands.

Required builder replay case families, each failing at a pinned consumer
line: (i) parametrizing a constant by width or size; (ii) changing each
literal numeral.

Rationale: finding P1-2. `family` is a free parameter of `ProgramContract`
unconnected to any run, `closed_uniform` discharges `uniform` for any closed
program, and the pins are `Nat` parameters, so a width-indexed family
`B : Nat -> Program` could be certified per member with literal numerals;
because `wordWidth n` is a function of `n`, width-indexing is size-indexing
(FK-5 re-entering through the width parameter). Coordinator ruling Q1 chose
two constants from one template with the padded leaf.

### V2-3 Emitted-cell extraction pin (AMEND-3, finding P1-3)

No version-1 sentence is superseded; version 1 never defined "emitted
cells".

Version 2: `efficientBuild xs` is defined inside the firewalled import
closure as a positional projection of the accepted run's final memory,
`emitted final outBase len`, where `final` is the final state of the
accepted run, `outBase` is the halt value and `len = extent - outBase`. It
is never defined through a function naming `buildMemory`, `cartesianShape`,
`metadata` or any semantic builder, and never through an intermediate
adapter store. `efficientBuildWord xs` is defined likewise from the
word-model run. The equality theorems `efficientBuild_eq_buildMemory` and
`efficientBuildWord_eq_buildMemory` have this syntactic left-hand side.

Rationale: finding P1-3. Version 1 pinned the right-hand side and both
initial states but not how the list is read out of the final
`Memory := Nat -> Option Nat`; a builder outside the firewall could have
defined the list from `buildMemory` itself or routed it through a semantic
adapter, closing REQ-PRE-EXACT against a list that is not the positional
content of the cells the run wrote, and running the PQ1 query on a sibling.

### V2-4 C3 gate reach and layered firewall (AMEND-4, finding P2-1, ruling Q4)

Supersedes (CONTRACT.md version 1, lines 139-140):

```text
Future Program/Run files must extend the explicit
firewall only with reviewed primitive-only modules, before builder acceptance.
```

Version 2: `scripts/preprocessing_contract_firewall.ps1` and
`docs/internal/extensions/pre1/primitive_manifest.json` stay byte-identical;
their surfaces are frozen by the 18-case contract registry (cases C17 and
C18). The builder gets a LAYERED guard
`scripts/preprocessing_builder_firewall.ps1` with
`docs/internal/extensions/pre1/builder_manifest.json` version 1. The
layered guard first invokes the contract guard unchanged and requires its
PASS, then checks the exact allowed-imports table of the operational modules
(`Program`, `Calculus`, `Safety`, `Structured`, `Compiler`, `Loop`,
`ArrayRun`, `Builder/*`) and the full transitive import closure of those
modules against {Std, Primitive, Input, Model, earlier closure modules},
and checks their strict-UTF-8, CRLF-to-LF normalized SHA-256 hashes from the
builder manifest. Future operational modules enter only through that layered
guard and its manifest, never by editing the contract guard.

Two checkers are added to `scripts/gate.ps1` (roster `expectedCheckers` and
`Invoke-Checker` call sites, following the existing pattern exactly):
`PRE1-CONTRACT-GATE` runs `scripts/preprocessing_contract_firewall.ps1`,
then `lake build RMQ.Core.WordRAM.Construction.Contract`, then
`lake env lean scripts/preprocessing_contract_check.lean`;
`PRE1-BUILDER-REPLAY` runs `scripts/preprocessing_builder_replay.ps1` in
full under its own measured deadline, chosen with at least 2x margin over
the recorded duration. The roster grows from 18 to 20 and the GATE COVERAGE
self-check must report 20 of 20.

Strengthened, not superseded (CONTRACT.md version 1, lines 148-149):

```text
The replay invokes this production guard before
compilation, without weakening the repository aggregate gate.
```

Version 2 reading: both guards (contract and layered builder) are invoked by
their replays before compilation and are now also reached by the repository
aggregate gate through the two checkers above.

Rationale: finding P2-1. At the audited commit no gate or CI reached the
firewall, the contract build or the typed consumer (the default `lake build`
root does not import `RMQ.Core.WordRAM.Construction.*`), so the aggregate
PASS was silent about these modules and the historical O-FIREWALL
"CI-enforced" property had lapsed. Coordinator ruling Q4 fixed the layered
shape so the contract guard stays untouched.

### V2-5 C3 placement of the accepted-program predicates (recommendation R3, finding P3-2)

Version 2: `Program`, `Uniform`, `programWords` and `CodeAccounting` stay in
Controls.lean and are consumed only from outside the operational closure
(Contract.lean and Capstone.lean). The firewalled modules operate on
`List BInstr` literally (`Program` is an abbreviation for `List BInstr`, so
a consumer identifies the two by `rfl`); no sibling `Uniform`,
`programWords` or `CodeAccounting` may appear inside the closure.

Rationale: finding P3-2. Controls.lean imports `RMQ.Core.Shape` and hosts
the deliberately forbidden oracle, so a firewalled run module cannot import
it; stating the placement prevents a duplicate uniformity predicate inside
the closure that the contract's controls would not cover.

### V2-6 Safety vocabulary (recommendation R1, finding P2-2)

Version 2: There is a single per-transition safety judgment
`Prim.Safe width s p` covering: operand fit; arithmetic result `< 2^width`;
`sub` non-underflow; positive `div`/`mod` divisor; `shl`/`shr` operand
`< width`; `store`/`load` address `< extent` with a present cell and value
`< 2^width`; `loadKey` present key; `reserve` with `extent + 1 < 2^width`;
branch/jump targets `< program length`; no `jumpRegister`. `Run.Safe` is:
every transition of the run is `Prim.Safe` and every post-state fits the
width. Fault-freedom is part of `Safe`: a safe transition never produces
status fault. This is the Safety.lean module of Stage 0 and the ONLY safety
vocabulary used in later stages; C2's sentence that later safety proves no
overflow, underflow, zero division or oversized shift on accepted runs is
discharged through this judgment and through no ad hoc bound.

Rationale: finding P2-2. `Arithmetic.eval` is the accepted PQ1 evaluator
over unbounded `Nat`, so one `shl` or repeated `mul` can create a huge
register in one charged tick; FK-3, FK-12, FK-14 and
INV-INSTRUCTION-ATOMICITY all rest on this one future row, and the audit
asked that its shape be named before the builder is written.

### V2-7 Route-study entries accepted by the coordinator

Each clause below is an append-only contract entry accepted from the builder
route study (`BUILDER_PLAN.md`).

V2-7.1 Temporary buffer. The bit-per-cell temporary buffer (one 0/1 numeric
cell per emitted bit, later Horner-packed into output words) is accepted
O(n)-word temporary workspace under REQ-PRE-COST; compressed temporary bits
are not required.

V2-7.2 Work unit. Executed work is the number of interpreter transitions
through `checkedStep`, partitioned over the ten `Prim.category` values
(`read`, `register`, `arithmetic`, `comparison`, `branch`, `control`,
`write`, `allocation`, `keyRead`, `oracleComparison`); `reserve`, `store`,
`loadKey`, `compareKey` and padding `move` no-ops are each one unit.

V2-7.3 Input account. The input account names n+1 numeric cells (word
model) or 1 numeric cell plus n key-bank cells (comparison model). Input
materialization is outside the builder boundary: the builder performs zero
input writes, which resolves the version-1 conditional "if materialization
is included in the builder boundary" in the negative. The retained input is
never stored to. The historical peak extent, including the output region,
is reported beside the temporary bound.

V2-7.4 Finite-key premise. The finite-key corollary premise is
`InputFits (wordWidth xs.length) xs`, with the all-size family
`List.replicate n 0` via `zero_inputFits` at width `wordWidth n`.

V2-7.5 Validation evaluator. Fixtures execute an array-backed evaluator
(registers, memory, keys and keyRegs as arrays) with a proved abstraction
theorem `runArray_abstract` to the mathematical run; expected values come
from `buildMemory xs` and its reference segments only.

V2-7.6 Quadratic-mutation control. The repeated-prefix/quadratic-mutation
control is a proof-level registry case (the cost theorem fails to
elaborate) plus an informative runtime cost check.

V2-7.7 Payload-bypass control. The table/program payload bypass control is
realized by the builder firewall hash surface plus the exactness theorem.

V2-7.8 Registries. The contract registry version 1 (18 cases) and its
runner are untouched and re-run as regression; the builder gets
`builder_cases.json` version 1 with its own runner.

### V2-8 Coordinator rulings on the route study's open questions (binding)

(Q1) Two constants from one template as in V2-2; the padded leaf is
recommended.

(Q2) The contract aggregate has PASSED on `c1c970b` and the contract audit
has PASSED with amendments, so Stage 0 is authorized now; the next aggregate
gate runs only on the frozen final builder candidate.

(Q3) INV-GLOBAL-PHYSICAL-MACHINE for the composed builder-plus-query is
satisfied by (a) positional store provenance for every output cell on
`[outBase, extent)`, (b) the accepted PQ1 capstone transported over the list
equality `efficientBuild xs = buildMemory xs`, and (c) a lifted Conservative
simulation of the accepted query program in the new ISA on the detached
emitted list. An offset-relocated in-place query execution is NOT required
and is recorded as an explicit limit in Capstone.lean comments, the matrix
evidence row and the report.

(Q4) Layered builder firewall as in V2-4; the contract guard is untouched.

(Q5) Per-module focused builds with an initial 600 s budget revised on
evidence; the builder replay is the focused gate and becomes a gate checker;
the aggregate is coordinator-scheduled on the frozen final candidate; the
validator executable is built by the gate's lakefile-derived exe stage and
executed by the builder replay.

(Q6) Metadata words that are emitted-segment offsets or lengths MAY be
produced from charged cursor snapshots taken during emission, with equality
to the metadata shape proved through segment-length lemmas;
INV-PROGRAM-ACCOUNTING is satisfied because they are computed data of the
same charged run.

(Q7) Crude explicit literals are acceptable (C in the hundreds to low
thousands, Cw around 10-14); no tightness or optimality is claimed anywhere.

(Q8) Headlines alias and claim-policy vocabulary are coordinator follow-up;
only one dated FAMILY_SUMMARY entry and one DIGESTION_LOG entry are added,
phrased as candidate status pending audit.

(Q9) `decide`/`rfl` are allowed only for tiny pure reference lists and for
literal pins on the compiled program list; machine runs are validated
through the array-backed executable, never by kernel evaluation;
`native_decide` and `Lean.ofReduceBool` remain banned.

(Q10) A stalled stage may be committed as checkpoint theorems with a
recorded INCOMPLETE status and independent later stages may proceed; a
checkpoint is never completion and only the coordinator re-plans.

The version-1 body above is retained byte-identical as history; where a
version-2 clause supersedes a version-1 sentence, the version-2 clause
governs.

## Version 3 amendments (2026-09-13, after continuation audit PRE-1-A1C)

Status: append-only version-3 entries, text only. They freeze, before stage S2
begins, the future builder surfaces that the continuation audit PRE-1-A1C
(verdict CONTINUATION_PASS_WITH_CONDITIONS on
`5f325ddb856b9095d1ad2aacc0bc69eda571d447`; report
`2026-09-13_PRE1_contract_continuation.md`, 84,923 bytes, SHA-256
2650BA3CC8CF8DDEB58E53DDC45121DFB127E0728B957A2FD540AD8B779B6A0A, sections 2-4)
found pinned only in prose (finding P2-1, condition C1), and they record the
coordinator's acceptance of conditions C1-C3. Nothing in the version-1 body or
the version-2 amendments above is edited; where a version-3 clause refines a
version-2 clause, the version-3 clause governs. No declaration named here
exists at this revision; every clause is an obligation of the stage named in
it, and deviating from a clause requires a later append-only amendment.

Names follow V2-2 (coordinator resolution of audit finding P3-3): `builderProgram`
is the comparison-oracle constant and `builderProgramWord` is the word-model
constant; the builder plan's `buildProgramKey`/`buildProgram`/`buildBudget` are
renamed to `builderProgram`/`builderProgramWord`/`builderBudget` in
BUILDER_PLAN.md in the same commit as this entry. Register literals below are
decimal `Operand` numerals.

### V3-1 Host module, namespace and mechanical location check (C1(a))

The declarations `builderSource : Structured.Block → Structured.Block`,
`builderBody : Structured.Block → Structured.Block` (V3-3),
`keyLeaf : Structured.Block`, `wordLeaf : Structured.Block`,
`builderProgram : List BInstr`, `builderProgramWord : List BInstr`, the fuel
function `builderBudget : Nat → Nat`, `efficientBuild : List Int → List Nat` and
`efficientBuildWord : Nat → List Int → List Nat` are declared in
`RMQ/Core/WordRAM/Construction/Builder/Program.lean` (module
`RMQ.Core.WordRAM.Construction.Builder.Program`), in namespace
`RMQ.SuccinctFinal.PackedConstruction`. That file is a key of the builder
firewall's allowed-imports table with a `builder_manifest.json` hash.

Mechanical check: the builder typed consumer `scripts/preprocessing_builder_check.lean`
contains one `run_cmd` that fails elaboration at its own lines unless
`Lean.Environment.getModuleIdxFor?` maps each of the nine fully qualified names
above to module `RMQ.Core.WordRAM.Construction.Builder.Program`. A registered
relocation case moves `efficientBuild` out of `Builder/Program.lean` into a
consumer-side module in the same namespace, runs through the per-mutation
manifest re-hash of V3-7 (condition C3), and is rejected at exactly the
`run_cmd` line set of the consumer. Due: the check and the case land with the
declarations (S7), and no later than the C3 mechanism.

Rationale: finding P2-1 scenario (4); the firewall sees imports and hashes, not
where a declaration is defined.

### V3-2 Parameterlessness pins (C1(b))

The builder typed consumer contains exactly these two lines:

```lean
example : List BInstr := @builderProgram
example : List BInstr := @builderProgramWord
```

Rationale: finding P2-1 scenario (1) and probes P-6/P-6n: an unapplied pin or an
`rfl` length pin admits an optional parameter such as `(w : Nat := 64)`; the
`@` form does not.

### V3-3 Definitional shape of the constants and the leaves (C1(c))

Both constants are one literally stated compiled form of `builderSource`,
pinned by `rfl` in the builder typed consumer:

```lean
theorem builderProgram_def :
    builderProgram = (builderSource keyLeaf).compileAt 0 ++ [⟨.halt 3⟩] := rfl
theorem builderProgramWord_def :
    builderProgramWord = (builderSource wordLeaf).compileAt 0 ++ [⟨.halt 3⟩] := rfl
```

Both leaves are literal five-action right-nested sequences, pinned by `rfl`:

```lean
theorem keyLeaf_def : keyLeaf =
    .seq (.action (.loadKey 0 4)) (.seq (.action (.loadKey 1 5))
      (.seq (.action (.compareKey 6 0 1)) (.seq (.action (.move 6 6))
        (.action (.move 6 6))))) := rfl
theorem wordLeaf_def : wordLeaf =
    .seq (.action (.arithmetic .add 7 4 2)) (.seq (.action (.load 7 7))
      (.seq (.action (.arithmetic .add 8 5 2)) (.seq (.action (.load 8 8))
        (.action (.comparison .lt 6 7 8))))) := rfl
```

Leaf register interface (fixed now): register 4 holds the index `i`, register 5
the index `j`, the leaf writes `[xs[i] < xs[j]]` into register 6; register 2
holds the constant 1 whenever a leaf runs; registers 7 and 8 are word-leaf
scratch; key registers 0 and 1 are key-leaf scratch; register 3 holds the halt
value `outBase`. The key leaf's two `move 6 6` instructions are the padding
no-ops of V2-2 and are charged one unit each (V2-7.2). `builderSource leaf`
begins with the header action, so `builderSource leaf = .seq (.action (.load 1 0)) (builderBody leaf)`
for a `builderBody` in the same module, and neither constant contains any
other instruction outside `builderSource`'s compiled form and the final
`halt 3`.

Rationale: finding P2-1 scenario (2) and section 4.3 item 3 of the audit.

### V3-4 Leaf difference with contents (C1(d))

The builder typed consumer states, at literal lists `P : List Nat`,
`K : List (Option BInstr)` and `Wd : List (Option BInstr)` written as numerals
and instruction literals:

```lean
theorem builder_leaf_difference :
    builderProgram.length = builderProgramWord.length ∧
    (List.range builderProgram.length).filter
        (fun i => builderProgram[i]? ≠ builderProgramWord[i]?) = P ∧
    P.map (fun i => builderProgram[i]?) = K ∧
    P.map (fun i => builderProgramWord[i]?) = Wd
```

proved by `decide` or `rfl` on the compiled lists (a literal pin on the compiled
program list under ruling Q9). Each occurrence of the leaf contributes five
consecutive positions, and the corresponding entries of `K` and `Wd` are the
five instructions of `keyLeaf` and `wordLeaf` of V3-3 in order.

Rationale: finding P2-1 scenario (2) and finding P2-2: positions alone leave the
leaf instructions unconstrained.

### V3-5 Contract instances with literal numerals (C1(e))

The builder typed consumer restates both instances with numerals:

```lean
theorem builderProgram_contract :
    ProgramContract builderProgram (fun _ => builderProgram) L B := ...
theorem builderProgramWord_contract :
    ProgramContract builderProgramWord (fun _ => builderProgramWord) L B' := ...
```

where `L`, `B`, `B'` are decimal numerals (one `L`, because V3-4 fixes equal
lengths), and the producer proves `builderProgram.length = L`,
`programWords builderProgram = B` and `programWords builderProgramWord = B'` by
`rfl` on the compiled lists. `family` is definitionally `fun _ => <constant>`
(V2-2).

### V3-6 Extraction bodies (C1(f)), refining V2-3

`efficientBuild` and `efficientBuildWord` have exactly these bodies, and the
builder typed consumer pins both by `rfl` at every `xs`:

```lean
def efficientBuild (xs : List Int) : List Nat :=
  match (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.status with
  | .halted outBase =>
      emitted (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final outBase
        ((run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.extent - outBase)
  | _ => []

def efficientBuildWord (width : Nat) (xs : List Int) : List Nat :=
  match (run builderProgramWord (builderBudget xs.length) (wordInputState width xs)).final.status with
  | .halted outBase =>
      emitted (run builderProgramWord (builderBudget xs.length) (wordInputState width xs)).final outBase
        ((run builderProgramWord (builderBudget xs.length) (wordInputState width xs)).final.extent - outBase)
  | _ => []
```

The consumer pin of the word body is stated at `width := wordWidth xs.length`,
and the required theorems have exactly these left-hand sides:
`efficientBuild_eq_buildMemory : ∀ xs : List Int, efficientBuild xs = buildMemory xs`
and
`efficientBuildWord_eq_buildMemory : ∀ xs : List Int, InputFits (wordWidth xs.length) xs → efficientBuildWord (wordWidth xs.length) xs = buildMemory xs`.
The fuel function body is `builderBudget n = C * n + D` with decimal numerals
`C`, `D` pinned by `rfl` in the consumer at S8. The non-halting branch is the
empty list, so a run that does not halt cannot project cells from address 0.
Neither body names a declaration outside the builder closure.

Amendment V3-6a (2026-09-13, coordinator ruling R-S7-5, record
`extension-coordination-20260911/claude-coordinator-20260912/PRE1_S7_V36_RULING.md`,
4,240 bytes, SHA-256 B355736C0B77E805148E0169390AF20E2B12A7EDB47E797B5CA106D2648800A0).
The fuel sentence above is superseded; nothing else in V3-6 changes.
Superseded text: "The fuel function body is `builderBudget n = C * n + D` with
decimal numerals `C`, `D` pinned by `rfl` in the consumer at S8."
Replacement: the fuel function body is `builderBudget n = D + C * n` with
decimal numerals `D`, `C` pinned by `rfl` in the consumer at S8; the producer
proves `builderBudget_eq_mul_add : ∀ n, builderBudget n = C * n + D`
propositionally (commutativity or `omega`, never `rfl` or `decide`) and the
stage consumer restates it at full type. Crude literals remain acceptable
(ruling R-S7-4); fuel sufficiency is proved for every `n` from the stage cost
theorems; no other fuel-body variant (irreducible wrapper, well-founded fuel)
is admitted. Every other V3-6 requirement stands: both extraction bodies exactly
as written, their `rfl` pins at every `xs` (the word pin at
`width := wordWidth xs.length`), both equality theorems at their exact left-hand
sides, the empty list on the non-halting branch, and closure-only names.
Reason: checking any definitional unfolding of the extraction bodies makes the
Lean 4.22.0 kernel reduce the match discriminant, and `Nat.add` recurses on its
second argument, so a trailing literal in the fuel is peeled one successor at a
time. Reproduction tables: worker log BUILDER_STAGE_LOG.md S7-14..S7-16 (builder
template: `1000000000 * n + 1000000000` kernel deep recursion; `C * n + 1000`
and `C * n + 10000` pass; one-instruction program: `C * n + 100000` fails;
`1000000000 + 1000000000 * n` passes with both exactness theorems) and the
coordinator's import-free reproduction `pre1-v36-repro/` (toy machine:
`1000000000 * n + 1000000000`, `1000000000 * n + 10000` and
`1000000000 * (n + 1)` fail at the `rfl` pin; `1000000000 + 1000000000 * n`
passes). The proven work bound at `n = 0` is about `8.4 * 10^8`, so no trailing
literal small enough for the kernel is admissible.

Refinement recorded: the audit's C1(f) text writes the word width inside the
body. `wordWidth` is defined in `RMQ.Core.WordRAM.Packed.Allocation`, which the
builder firewall does not admit into the closure, so `efficientBuildWord` takes
the input model's encoding width as its first explicit argument. The width is
an argument of the input model's initial state, not of the program: the
program constant `builderProgramWord` stays parameterless (V3-2). The consumer
pin and the equality theorem fix the width to `wordWidth xs.length`. This
supersedes the extraction sketch of BUILDER_PLAN.md S7 (`r.result.getD 0`).

Rationale: finding P2-1 scenario (3) and finding P3-4 (`emitted` reads absent
cells as 0; output-cell presence is carried by the Q3(a) provenance field of
the capstone).

### V3-7 Replay-case shapes for V2-2 (i) and (ii) (C1(g))

(i) Parametrization. Two registry mutations of `Builder/Program.lean`, one per
constant, replacing `def builderProgram : List BInstr :=` by
`def builderProgram (w : Nat := 0) : List BInstr :=` (respectively for
`builderProgramWord`). The producer still elaborates. The case runs through the
per-mutation manifest re-hash of condition C3 (the re-hash is confined to the
mutation and the committed manifest is unchanged after restoration), and it is
rejected at the consumer with a failing line set equal to exactly the
corresponding `@` line of V3-2.

(ii) Numerals. One registry mutation per consumer numeral: `L`, `B`, `B'`, each
element of `P` in V3-4 and, at S8, `C`, `D`, `Cw` and `Dw`. Each changes that
numeral in `scripts/preprocessing_builder_check.lean` only and is rejected at the
consumer with the exact failing line set of the theorem stating it. Numeral
changes in producer files stop at the firewall or producer and do not
substitute for these cases.

### V3-8 Word-model qualification of V2-1 (C1(h)); recorded limit

`HeaderUse` certifies, in both input models, that the accepted run's first
transition is the header load into register 1, that register 1 is never
written again, and that the run faults after one transition when cell 0 is
absent. In the word model it does NOT certify that the output depends on the
loaded header value: `reserve` returns the extent, which is `n + 1` in the word
model, and a program with `HeaderUse` can return `n` from the extent (audit
probes P-1/P-2). In the comparison-oracle model the extent starts at 1, and the
only length source is cell 0 (probes P-3/P-4), so exactness of the primary
witness `builderProgram` forces header use. The word constant's use of the
header is inherited only through the shared template and the leaf pins
(V2-2, V3-3, V3-4). This is a recorded limit, not a claimed theorem; no
value-dependence theorem is required.

### V3-9 Discharge of `tailNeverWritesR1` at the constants (C1(i)); refining V2-1(b)

At both constants, `∀ i ∈ builderProgram.tail, WritesOnly (fun r => r ≠ 1) i`
(respectively `builderProgramWord`) is proved by `Structured.Block.compile_writesOnly`
from `(builderBody leaf).WritesOnly (fun r => r ≠ 1)` (V3-3) at the leaf in
question, plus the destination-free final `halt 3`. The `Block.WritesOnly`
facts are proved compositionally from per-phase source lemmas by structural
simplification (`Block.WritesOnly`, `Action.prim`, `Prim.destination?` and
literal register disequalities); `keyLeaf.WritesOnly (· ≠ 1)` and
`wordLeaf.WritesOnly (· ≠ 1)` may be decided on their five actions. A kernel
`decide` over the whole compiled list or over a whole source template is NOT
used for this field. V2-1(b)'s "checked by `decide`" is superseded by this
clause (audit finding P3-3: a list-wide decision over several thousand
instructions is not covered by ruling Q9a).

### V3-10 Coordinator acceptance of conditions C2 and C3 and recommendations

(C2) Before S7 instantiates `HeaderUse` at `builderProgram` and
`builderProgramWord`, the builder registry gains `B14_HEADERFIRST_CONSUMER`
exactly as specified in audit section 2 (condition C2): `headerFirst : True`
with the run-level fields supplied from `headerUse_of_program`'s hypothesis,
expected consumer surface `preprocessing_builder_check.lean:20:`.

(C3) Before S7 registers the constants' cases: a per-mutation manifest re-hash
confined to the mutation, so a closure-module mutation can reach the producer
and consumer stages, and V3-7 case (i) through it. Before the S8 candidate is
frozen: consumer-reaching weakening, deletion or sibling cases for the
foundation declarations the capstone consumes (`EvalG.compile_realizes`,
`SafeEval.compile_safe`, `run_write_at`, `run_load_at`, `writes_replay`,
`run_agree_of_reads`, `RunsTo.fuel_extension`, `Prim.Safe`/`Run.Safe`,
`runArray_abstract`) with exact line-set surfaces. With C3: the contract guard
launched by the builder firewall gets its own deadline (audit P3-7), and both
typed consumers print their PASS marker only after successful elaboration
(audit P3-1).

Ruling Q9a, as recorded in the audit, stands. Every commit that adds or changes
public-facing or `docs/` text passes `scripts/claim_drift_scan.ps1 -Strict` with
default roots before the final candidate, and no raw claim-scanner hit log is
committed under a scanned root.

### V3-7a and V3-10a Amendment (2026-09-14, repair PRE-1-R2 after fresh blind audit PRE-1-A2)

Status: append-only version-3 amendment, text only; nothing above is edited.
Source: fresh blind audit PRE-1-A2 of `84ae12f6f6bad99fd3215c5bdd5b2a93e3779897`,
report `2026-09-14_PRE1_builder_fresh_blind.md` (53,979 bytes, SHA-256
bda5f41450dddaf4cec8fc898e63d99881a12fece96f4ccc476b3fa2f82ed180), findings P3-1
and P2-1; repair prompt `PRE1_R2_CONSUMER_MARKERS.md` (18,929 bytes, SHA-256
60499BD23101670392C011EA08B4D4B78C23FF9B6B629C655940CD43C9267C2B); repair
worker record `repair-r2/REPORT.md`.

V3-7a (placement of the `Cw` and `Dw` numeral cases; PRE-1-A2 P3-1). Superseded
text of V3-7 (ii): "(ii) Numerals. One registry mutation per consumer numeral:
`L`, `B`, `B'`, each element of `P` in V3-4 and, at S8, `C`, `D`, `Cw` and `Dw`.
Each changes that numeral in `scripts/preprocessing_builder_check.lean` only and
is rejected at the consumer with the exact failing line set of the theorem
stating it. Numeral changes in producer files stop at the firewall or producer
and do not substitute for these cases." Replacement: the `L`, `B`, `B'`, `P`,
`C` and `D` cases (B19-B34) stand as written. The `Cw` and `Dw` numeral cases are
`B50_CAPSTONE_CW_NUMERAL` and `B51_CAPSTONE_DW_NUMERAL`; each changes that
numeral in `RMQ/Validation/PreprocessingContract.lean` only (the capstone typed
consumer, theorem `check_comparisonRun_workspace`) rather than in
`scripts/preprocessing_builder_check.lean`, uses the builder replay's `capstone`
profile, and is rejected at that consumer with the exact failing line set of the
theorem stating it (`PreprocessingContract.lean:275:`). Reason: `Cw` and `Dw` are
the literals of `BuilderRunFacts.workspace`, which is exported only through
`ConstructionAndQueryCapstone`, whose exact-type consumer is the capstone
consumer. Stating them in the builder consumer would make that consumer import
the capstone and the stage proof tower, so every closure-module registry case
(B15-B18, B35-B42) would rebuild the tower twice (DD-20260913-PRE1-017,
DD-20260913-PRE1-018). The obligation's substance is unchanged: one
consumer-numeral mutation per numeral, rejected at the typed consumer that states
it with the exact failing line set; numeral changes in producer files do not
substitute for these cases.

V3-10a (typed-consumer verdict markers; PRE-1-A2 P2-1). Refined text of V3-10
(C3): "both typed consumers print their PASS marker only after successful
elaboration (audit P3-1)". Refinement: every PRE-1 typed consumer whose marker a
replay, gate checker or report reads (`scripts/preprocessing_builder_check.lean`,
`RMQ/Validation/PreprocessingContract.lean`, and the contract consumer
`scripts/preprocessing_contract_check.lean`, together with the spec and stage
consumers `scripts/preprocessing_spec_check.lean` and
`scripts/preprocessing_stage_check.lean`) prints its marker if and only if the
whole file elaborated with no error-severity message and its existing witness
(a witness exists and collects no `sorryAx`) and guard conditions hold. Reason:
the version-3 marker condition (the witness collects no `sorryAx`) printed the
marker on failing runs: in B16, B17 and B18 (a failing `@` example or `run_cmd`
not referenced by the witness), for the audit's probes CAB2 and CAB4 (checked
theorems absent after maximum-recursion-depth errors) and, reproduced on
`a0c93e9cf4d3c93856f5756ff6a7271da2b821ff` for all five consumers, for a failing
anonymous example, a failing `#guard`, a witnessed declaration failing with a
maximum-recursion-depth error, a failing declaration the witness does not
reference and a failing command after the marker. Mechanism: Lean 4.22.0 resets
the command state's message log before every command, so the marker command
elaborates the file a second time in-process from its own source text with only
itself blanked (`Lean.Parser.parseHeader`, `Lean.Elab.processHeader`,
`Lean.Elab.IO.processCommands`) and requires `MessageLog.hasErrors` to be false
for the header and every command. The contract consumer's change is confined to
its verdict-marker command and comment at the end of the file, so no contract
registry line moves; the contract registry, runner, firewall and manifest are
unchanged. The builder replay registry, version 2, additionally requires the
profile's marker to be absent from every consumer-stage rejection. The exit code
remains the verdict of every replay and gate checker. Control matrix:
`repair-r2/marker_controls.json` with `repair-r2/run_marker_controls.ps1`.

Conformance note (no amendment): V3-10 (C3) names `Prim.Safe`/`Run.Safe` among
the foundation declarations needing consumer-reaching cases; registry version 2
adds `B55_RUN_SAFE_LENGTH_WEAKEN`, rejected at the builder consumer's `Run.Safe`
definition pin, and the `halts` controls `B53_RUNFACTS_HALTS_WEAKEN` and
`B54_RUNFACTS_HALTS_FUEL_LARGER` for PRE-1-A2 P2-2.
