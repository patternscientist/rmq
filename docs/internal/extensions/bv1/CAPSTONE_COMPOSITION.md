# BV-1 capstone composition — frozen implementation contract

Owner: numeric_reader. Source checkpoint
645a0502b9da9ad6444edbe44759e1c2c5661f25; workflow governance
0e6a00f654abc64f8b68988fa9675b9a839dca2f. The canonical proof-sprint skill and
completion gate remain active in this continued governed task. Scope is NEW
Capstone.lean and this report only. Root owns the operation execution/API
repairs, independent public consumer, mutation campaign, final commit and
acceptance. Other agents own their disjoint leaves. No executable or shared
module changes; no compiler until explicit root slot grant.

The root's verbatim assignment is: "Implement exact
FullyChargedBitvectorCapstone + fullyChargedBitvectorCapstone_holds frozen in
CAPSTONE_SCHEMA.md, every seven required field groups on same objects, no
hypotheses in inhabitant." "Keep full target, no weakened fallback."

## Frozen expected type before source edits

The public namespace is RMQ.PackedBitvector. Field names are exactly the 23
names proposed by root. The structure is an unparameterized proposition.
Every field uses the actual canonical allocation and operation objects;
the constructor itself takes no arguments or hypotheses.

```lean
structure FullyChargedBitvectorCapstone : Prop where
  completeCapacity : ∀ bits : List Bool,
    ((Allocation.memory bits).length +
      ((program .access).map Instruction.encoding).flatten.length +
      ((program .rank).map Instruction.encoding).flatten.length +
      ((program .select).map Instruction.encoding).flatten.length +
      (8271 + 3)) * Experiment.width bits.length ≤
        bits.length + completeRho bits.length
  overheadLittleO : LittleOLinear completeRho
  widthBounds : ∀ n : Nat,
    Nat.log2 (n + 2) + 1 ≤ Experiment.width n ∧
      Experiment.width n ≤ 48 * (Nat.log2 (n + 2) + 1)
  memoryWordsFit : ∀ (bits : List Bool) (value : Nat),
    value ∈ Allocation.memory bits → value < 2 ^ Experiment.width bits.length
  readerGeometry : ∀ (bits : List Bool) (target : Bool) (regs : Registers),
    regs 3 = target.toNat → regs 22 = Experiment.width bits.length →
    NumericReaderGeometry (Allocation.memory bits) (Experiment.width bits.length) regs
  readerCorrect : ∀ (bits : List Bool) (target : Bool) (regs : Registers),
    regs 3 = target.toNat → regs 22 = Experiment.width bits.length →
    let actual := Experiment.physicalReader.eval (Allocation.memory bits) ⟨regs, .running⟩
    let expected := (Allocation.readStore bits target).readWord? (regs 8192) (regs 8193)
    actual.final.status = .running ∧
    actual.final.regs 8194 = logicalPacket expected ∧
    actual.final.regs 8195 = logicalLength expected ∧
    actual.reads = Allocation.readerReceipts bits target (regs 8192) (regs 8193) ∧
    ReaderFrame regs actual.final.regs
  accessCorrect : ∀ (bits : List Bool) (index : Nat), access bits index = bits[index]?
  rankCorrect : ∀ (bits : List Bool) (target : Bool) (endPos : Nat),
    rank bits target endPos =
      if endPos ≤ bits.length then some (Succinct.rankPrefix target bits endPos) else none
  selectCorrect : ∀ (bits : List Bool) (target : Bool) (occurrence : Nat),
    select bits target occurrence = Succinct.select target bits occurrence
  accessExecution : ∀ (bits : List Bool) (argument : Nat),
    let actual := execute bits .access false argument
    let packet := AccessProof.accessPacket bits argument
    actual.result = some packet ∧ actual.final.status = .halted packet ∧
    actual.final.regs 705 = packet ∧ actual.reads = accessExecutionReceipts bits argument ∧
    actual.steps ≤ 132
  rankExecution : ∀ (bits : List Bool) (target : Bool) (argument : Nat),
    let actual := execute bits .rank target argument
    let packet := rankPacket bits target argument
    actual.result = some packet ∧ actual.final.status = .halted packet ∧
    actual.final.regs 360 = packet ∧ actual.reads = rankExecutionReceipts bits target argument ∧
    actual.steps ≤ 1450
  selectExecution : ∀ (bits : List Bool) (target : Bool) (argument : Nat),
    let actual := execute bits .select target argument
    let packet := optionNatPacket (Succinct.select target bits argument)
    actual.result = some packet ∧ actual.final.status = .halted packet ∧
    actual.final.regs 513 = packet ∧ actual.reads = selectExecutionReceipts bits target argument ∧
    actual.steps ≤ 10030
  accessSafety : ∀ (bits : List Bool) (argument : Nat),
    argument < 2 ^ Experiment.width bits.length →
    RankExecutionSafety (Allocation.memory bits) (Experiment.width bits.length)
      (program .access) ((source .access).size + 1) (initial .access false argument)
  rankSafety : ∀ (bits : List Bool) (target : Bool) (argument : Nat),
    argument < 2 ^ Experiment.width bits.length →
    RankExecutionSafety (Allocation.memory bits) (Experiment.width bits.length)
      (program .rank) ((source .rank).size + 1) (initial .rank target argument)
  selectSafety : ∀ (bits : List Bool) (target : Bool) (argument : Nat),
    argument < 2 ^ Experiment.width bits.length →
    RankExecutionSafety (Allocation.memory bits) (Experiment.width bits.length)
      (program .select) ((source .select).size + 1) (initial .select target argument)
  programLengths :
    (program .access).length = 132 ∧
    (program .rank).length = 1450 ∧
    (program .select).length = 10030
  sourceBudgets :
    (source .access).size + 1 = 132 ∧
    (source .rank).size + 1 = 1450 ∧
    (source .select).size + 1 = 10030
  stepsBound : ∀ (bits : List Bool) (operation : Operation) (target : Bool) (argument : Nat),
    (execute bits operation target argument).steps ≤ instructionBound operation
  categoryPartition : ∀ (bits : List Bool) (operation : Operation) (target : Bool) (argument : Nat),
    let actual := execute bits operation target argument
    actual.steps = actual.categoryCount .memoryRead + actual.categoryCount .registerWrite +
      actual.categoryCount .arithmetic + actual.categoryCount .comparison +
      actual.categoryCount .branch + actual.categoryCount .control
  categoryBounds : ∀ (bits : List Bool) (operation : Operation) (target : Bool)
      (argument : Nat) (category : Category),
    (execute bits operation target argument).categoryCount category ≤ instructionBound operation
  finiteScratch : ∀ (memory : Memory) (operation : Operation) (target : Bool)
      (argument fuel r : Nat), 8271 ≤ r →
    (run memory (program operation) fuel (initial operation target argument)).final.regs r = 0
  suppliedMemoryAgreement : ∀ (bits : List Bool) (operation : Operation)
      (target : Bool) (argument : Nat) (supplied : Memory),
    (∀ receipt ∈ (execute bits operation target argument).reads,
      supplied[receipt.address]? = (Allocation.memory bits)[receipt.address]?) →
    run supplied (program operation) ((source operation).size + 1) (initial operation target argument) =
      execute bits operation target argument
  validArgumentFits : ∀ (n argument : Nat), argument ≤ n → argument < 2 ^ Experiment.width n

theorem fullyChargedBitvectorCapstone_holds : FullyChargedBitvectorCapstone
```

The first argument bounds use all natural numbers, including invalid
representable arguments. Access selects the false input bank; rank/select
quantify both targets. Safety alone requires argument representability.
The independent consumer must unfold NumericReaderGeometry and ReaderFrame,
retain all four actual descriptor reply hypotheses and request registers,
and expand all five RankExecutionSafety conjuncts. Packet and receipt helper
definitions remain the existing independent specifications and charged
source-derived lists. Program length, source budget and execution answer
fields expose all three literal bounds.

Root requested stable standalone BV1-FIELD-BEGIN/END and BV1-VALUE-BEGIN/END
comments around all 23 structure fields and constructor assignments. These
markers are present for exact-byte mutation of the public source copies;
they change no proposition. Root's separate consumer will project every
field from its required inhabitant.

## Frozen acceptance-to-evidence matrix

| ID | Verbatim schema requirement | Exact field group / intended source evidence | Non-vacuity challenge | Status |
| --- | --- | --- | --- | --- |
| CAP-1 | "Literal memory length plus the flattened Instruction.encoding length of each of the three compiled programs plus 8271+3 scratch words, all multiplied by W" | completeCapacity := complete_capacity; overheadLittleO := completeRho_littleO; widthBounds := width_bounds. Full literal inequality quoted above. | Deleting any code or scratch term must fail the independent capacity projection; root owns campaign. | CANDIDATE_COMPLETE |
| CAP-2 | "Every member of actual memory fits W"; "actual four loaded descriptor replies yield a safe computed position and strict logical stride bound"; "actual reader on this memory has exact packet, length, ordered actual descriptor/span receipts and register frame" | memoryWordsFit := canonical_memoryWordsFit; readerGeometry := canonical_numericReaderGeometry with two actual metadata equalities; readerCorrect := Allocation.physicalReader_correct with those same equalities. | Empty sentinel and out-of-range request registers remain quantified; no valid-index or readiness premise is added. | CANDIDATE_COMPLETE |
| CAP-3 | "access bits i=bits[i]?"; "rank bits target p=if p≤bits.length then some(rankPrefix target bits p) else none"; "select bits target k=Succinct.select target bits k" | accessCorrect := access_eq; rankCorrect := rank_eq; selectCorrect := select_eq. | All-natural API quantification includes arguments outside machine capacity. | CANDIDATE_COMPLETE |
| CAP-4 | "The actual run halts with the encoded independent specification, places that packet in the same result register used by the API, has the exact charged setup/controller receipts, and stays within the fixed literal instruction bound." | accessExecution/rankExecution/selectExecution := execute_access/execute_rank/execute_select with source_budget rewritten to 132/1450/10030. | A sibling run, missing setup receipts, or wrong API output register cannot match the quoted fields. | CANDIDATE_COMPLETE |
| CAP-5 | "For each operation and representable argument, the public consumer expands all five existing RankExecutionSafety conjuncts" | accessSafety/rankSafety/selectSafety := canonical operation execution safety. Same memory, program, source budget and initial state. | Invalid representable arguments remain covered; field fits include dormant instruction fields. | CANDIDATE_COMPLETE |
| CAP-6 | "Literal program lengths/budgets are access132, rank1450, select10030"; "Actual six category counts partition actual steps and each is bounded"; "Every fuel prefix of actual programs, even over arbitrary supplied memory, keeps every register at index≥8271 equal to zero" | programLengths/sourceBudgets := program_length/source_budget; stepsBound/categoryPartition/categoryBounds := matching Observations theorems; finiteScratch := run_finite_registers. | Scratch applies to arbitrary memory and all fuel, including faulty loads; categories refer to actual transitions. | CANDIDATE_COMPLETE |
| CAP-7 | "Agreement at every attempted receipt, including absent replies, implies equality of the complete actual run on supplied memory." | suppliedMemoryAgreement := execution_eq_of_agree; validArgumentFits := valid_argument_fits supports valid machine inputs. | Agreement uses Option replies at every attempted read; complete Run equality retains result/transitions/cost/receipts. | CANDIDATE_COMPLETE |

The original 30-row whole-client acceptance matrix remains untouched. These
seven groups inherit the IDs listed in CAPSTONE_SCHEMA.md, notably store
identity, program accounting, width scaling, global physical machine, value
dependency, execution trace, public composition and category separation.
Independent field-consumer and mutation certification remain explicitly root
owned, and no worker acceptance claim substitutes for them.

## Composition and verification plan

This leaf is a proof constructor over existing theorem statements. The root's
execution/API repair work and its independently authored consumer run in
parallel with this disjoint assembly; another subagent would duplicate those
responsibilities. No new data model or assembly path is introduced.

Once root grants the slot and InterfaceProof is warm, compile only Capstone
with the owned pinned Lean 4.22.0 helper, one job, initial warm deadline 180
seconds. Run narrow repairs as needed. Record exact source hashes, endpoint
axiom inventory and stage output. Root checks its separate expanded public
consumer and mutation cases. Run scoped and full trust/native scans plus
git diff --check. Root owns aggregate/design/public certification.

## Evidence and proof digestion

The draft constructor has one direct assignment per frozen field, and all
23 field/value marker pairs have matching unique names and order. The
whole-client matrix SHA256 remains
80BD59A314FD33D37076802954444DA24F65C87A2A91DE23BC668B6AF9CCEB24.
Source and independent public consumer checks have passed at the exact
hashes recorded below. No assigned constructor field remains open.

Conceptually, the capstone bundles independently proved facts without adding
an alternate allocation, execution model or program. Complete capacity uses
the literal actual memory and all three encoded programs. The reader fields
connect those memory words to the logical read store. The API and compiled
answer fields connect the original bitvector specification to the actual
output registers. Safety and cost fields use those identical runs, while the
finite-scratch field is stronger in its memory domain and covers arbitrary
supplied memory at every fuel count.

In plain English, the intended inhabitant says one stored bitvector supports
access, rank and select with the specified answers, charged reads and finite
machine bounds, while counting all retained data, program code and scratch.
The inhabitant itself has no premises. Inside it, physical safety applies to
representable machine arguments, reader correctness assumes its two numerical
input metadata values, and supplied-memory equality assumes agreement at the
actual attempted addresses. Those explicit field-local conditions preserve
the respective operational contracts; the all-natural APIs need no such
premises.

A skeptical reviewer should check that dropping a counted term, replacing a
run, changing an output register, removing a safety conjunct or losing an
attempted failed reply is detected at the independent public projection.
Root owns that checked consumer and mutation campaign. This constructor's
stable markers make those exact source mutations possible without changing
the unmutated propositions or accepting a constructor-only failure.

No new representation, oracle, cost rule or workflow choice is introduced.
The public record shape and mutation markers implement the root's frozen
schema and explicit naming request. Root owns any corresponding branch-level
design/public documentation and the final exact-commit audit.

## Final constructor evidence

Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

All seven frozen constructor groups above are inhabited without premises by
fullyChargedBitvectorCapstone_holds. The root-authored independent public
consumer projects all 23 fields and the exact inhabitant; every projected
proposition passed. This is constructor/consumer completion for the assigned
leaf. Root's public mutation certification, executable validation, aggregate
gate and exact-commit blind audit are explicitly separate responsibilities.
No mutation rejection is claimed in this report.

| Evidence stage | Result | Exact scope |
| --- | --- | --- |
| capstone-build-v1 | PASS, exit 0, 9.170 seconds / 180 | Targeted warm Capstone build; first attempt; no own warnings. |
| capstone-public-consumer-v1 | FAIL, exit 1, 11.030 seconds / 180 | Only the select packet projection needed proof conversion from Option.map/getD to the independently written match. All other field projections passed; no theorem or field type changed. |
| capstone-allocation-reader-consumer-v1 | PASS, exit 0, 8.770 seconds / 180 | Root's independent allocation/reader consumer and all 14 requested axiom inventories. |
| capstone-public-consumer-v2 | PASS, exit 0, 15.320 seconds / 180 | Root made the proof-only cases/simpa repair; all 23 projected fields plus the exact public inhabitant now pass. |
| capstone-static-final | PASS | Full trust/native scans have no matches; owned source conflict/debug/trailing-space scan has no matches; working-tree diff check and exact-base committed-range check exit 0; all 23 marker names unique and aligned. |

All compiler stages used the owned kill-on-close helper, pinned Lean 4.22.0,
LEAN_NUM_THREADS=1 and the exact deadlines shown. Durable command records are
commands/<stage>.json, with complete command arguments/output, source hashes,
process ownership and no timeouts. The capstone and all 24 public consumer
inventories contain only [propext, Classical.choice, Quot.sound]. In the
allocation/reader consumer, completeRho_littleO and width_bounds use only
[propext, Quot.sound]; its other inventories use the standard three axioms.
The transient failed consumer elaboration is not acceptance evidence.

The exact checked Capstone.lean SHA256 is
1C6CD0A85B77FBA7706C77DA87DE358808A24FA661D5635A3C4B3BBF96005D69.
The root-owned public_expected_type.lean SHA256 is
FEA8D045EF0A9CB9679949ED8825F2E04A4542C01E8F056A778BB0B474BF7A9E.
The root-owned allocation_reader_expected_type.lean SHA256 is
DD09511ED00D8753C97164EEE06CC0E58C066CB0BFE33C0A37CA04D2C6D8F7ED.
Capstone.olean is 110,088 bytes. No capstone source changed after its first
successful build. The whole-client frozen matrix still has the hash above.

No source, peer consumer or shared module was changed by this leaf. Root
applied the only public consumer proof repair. The build slot was released
after the final consumer, and no owned process remains. Per explicit root
instruction, these files are not separately committed; the exact-base range
check is empty at the assigned HEAD and does not substitute for root's final
committed-range/design/public certification. Broad gates were not repeated
for this narrow proof constructor.
