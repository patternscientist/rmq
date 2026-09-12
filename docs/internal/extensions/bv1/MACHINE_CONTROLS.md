Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

## Frozen contract before implementation

This continues the preflighted generic-controller worker at checkpoint645a0502b9da9ad6444edbe44759e1c2c5661f25 and governance0e6a00f654abc64f8b68988fa9675b9a839dca2f. The only new implementation files owned by this leaf are scripts/packed_bitvector_machine_controls.lean and scripts/packed_bitvector_machine_controls.ps1, plus this report and task-local command evidence. The actual Source, Allocation, main validator46-case registry, probe and selector scripts remain owned elsewhere and unchanged by this worker.

The root's exact target is replayable controls on the actual Source programs and Allocation.memory: actual result changes after one supplied-memory cell changes; independently literal original packets; empty supplied-memory faults at the first setup read; a dormant oversized instruction rejected by the whole-program Instruction.Fits predicate while preserving the reachable packet; an exact nonempty versioned registry; omitted/valid/empty/whitespace/malformed/unknown selectors; bounded process ownership; expected verdict/failing surface; timestamped replay; source restoration and clean checks. This is not the root's public certificate/consumer mutation campaign.

Before implementation the root corrected the access fixture: "physical cell207 contains the raw first bit plus following densely packed components. Amend the access control before implementation to flip ONLY its least-significant raw bit: let originalCell=canonical memory[207], require originalCell%2=0, write originalCell+1, assert actual packet1->2 and report exact cell values. My earlier literal0->1 was an inaccurate test detail, not a frozen user requirement; do not erase other component bits. Rank cell2 and select cell0 scalar mutations remain literal1->0. Registry12 + selector8 approved; preserve this precise rationale/amendment in control contract. No endpoint fallback."

The version1 Lean registry is frozen in this order:

1. access-original: actual [false], access false index0, literal packet1.
2. access-raw-cell: same actual canonical baseline, replace cell207 by its original even value+1, literal packet2.
3. rank-original: actual [false], rank false prefix1, literal packet2.
4. rank-length-cell: replace scalar cell2 from literal1 to0, literal packet0.
5. select-original: actual [false], select false occurrence0, literal packet1.
6. select-count-cell: replace scalar cell0 from literal1 to0, literal packet0.
7. access-empty-memory: actual access program and initial state, supplied memory[], fault on transition1 instruction load16 6, exact reads[receipt0 none], result none.
8. rank-empty-memory: same empty-memory specification for actual rank program.
9. select-empty-memory: same empty-memory specification for actual select program.
10. access-dormant-oversized: append constant0(2^W) after the actual program's halt; baseline literal packet1 is preserved, original whole-program Fits accepts and appended program Fits rejects exactly the appended instruction.
11. rank-dormant-oversized: same, baseline literal packet2.
12. select-dormant-oversized: same, baseline literal packet1.

All runs use runArray at the same exact Source.program compile result, with the existing runArray_toArray equality as a checked expected-type consumer. The dormant fixture is the only altered supplied program and appends a single instruction after the canonical halt; canonical Source.program remains unchanged. Whole-program Fits is the accepted predicate P for both baseline and mutated supplied programs. Executed-instruction Fits is a separately reported weaker predicate; preserving that weaker predicate does not count as refuting P. The Boolean checker must be proved equivalent to the actual Instruction.Fits predicate.

For the three memory mutations, the unchanged accepted predicate P is packetOK for the independently literal original packet, applied to the actual returned Run. The canonical baseline must satisfy P and the single-cell mutant must reject the same P, while satisfying the independently literal changed packet. A fixture PASS means these expected accept/reject verdicts were observed; it is not a claim that the noncanonical mutated memory satisfies the canonical semantic theorem. Details report the original/mutated result projections and `canonical-packet-accepted=false` explicitly.

The version1 production-selector replay registry is frozen as omitted, valid(access-raw-cell), empty, whitespace, malformed(access raw), unknown(no-such-case), padded( access-raw-cell ), incompatible(Case plus ListRegistry). Expected exits are0 for omitted/valid and2 for the remaining six; omitted must execute all12, valid exactly1, invalid selectors must identify the exact selector-failure surface. Each replay uses a fresh timestamped evidence tag, so committed prior evidence cannot block a later replay.

## Acceptance matrix

| ID | Mandatory result | Current evidence |
| --- | --- | --- |
| MC-MEMORY | Three independently literal original packets plus three single-cell supplied-memory mutations, checked cell identities, same actual program, changed returned packet, memory-backed changed-cell receipts. | CLOSED: r18 omitted-selector output has the six exact PASS names. Raw cell207 changes158613695889408 to158613695889409 and packet1 to2; rank cell2 changes1 to0 and packet2 to0; select cell0 changes1 to0 and packet1 to0. Every mutation rejects packetOK(originalLiteral), accepts packetOK(changedLiteral), returns a different result, changes exactly one supplied cell and has both original/mutant read witnesses plus complete receipt backing. |
| MC-FAULT | Each actual operation faults at first setup load against memory[], with exact failed receipt0/none and no result. | CLOSED: r18 omitted-selector output passes all three empty-memory fixtures. Each actual final status is fault, result none, steps2 and reads exactly[{address:=0,reply:=none}]; transition1 additionally pins before.pc1, before.regs6=0, load16 6, after.status fault and that same failed receipt. |
| MC-STATIC | Same whole-program Instruction.Fits predicate accepts canonical code and rejects appended oversized operand; canonical reachable result and read observations persist, appended instruction is unreachable. | CLOSED: r18 omitted-selector output passes all three dormant fixtures. Width48 gives oversized operand281474976710656; original Fits=true and mutant Fits=false, with sole failing indices132/1450/10030. All executed PCs precede the original code length, all executed instructions fit, and packets1/2/1, ordered reads and steps equal the canonical baseline. The checked reflection equivalences and general static-rejection theorem below identify the exact predicate. |
| MC-REGISTRY | Exact versioned nonempty12-case registry, independent expected names/order/count; all8 production selector replays with exact expected exit/surface. | CLOSED: r18 records exactly omitted,valid,empty,whitespace,malformed,unknown,padded,incompatible, all passed. Omitted executes the exact ordered12 PASS names, valid executes only access-raw-cell, and all six invalid selectors exit2 at BV1-MACHINE-SELECTOR FAIL before Lean execution. Both Lean and PowerShell independently pin the exact12 names/order and nonempty cardinality. |
| MC-REPLAY | Owned bounded process trees, pinned toolchain1thread, timestamped versioned durable evidence, source hashes and scoped tracked-status restoration, no filesystem source mutation. | CLOSED: r17/r18 production evidence records134 source/dependency hashes before and after, exactRestoration=true, scopedStatusRestored=true and whitespaceCheck=true. Every owned child reports kill-on-close-job, no timeout and no output limit. Each run uses a fresh UTC/GUID evidence tag. The initial shared tree was dirty and is reported honestly; the executed source closure is unchanged. |
| MC-TRUST | Checked runArray bridge and actual-Fits checker equivalence; expected-type/static rejection proofs, trust/whitespace scans, proof digestion and exact scope caveats. | CLOSED: r16 elaborates the independent runArray equality example and four named theorems with only propext/Classical.choice/Quot.sound. r17 known selector and r18 full campaign pass. r20 records no forbidden declarations/Mathlib/native proof shortcuts, working-tree and exact committed-range whitespace success, unchanged frozen matrix SHA256 and parsed PowerShell source. Scope and digestion appear below. |

Verification will first check the new Lean file/startup under an exclusive root-granted build slot, then one known query selector(access-raw-cell), before any full replay, following B7R3-STARTUP-SMOKE-BEFORE-FULL-REPLAY. The production8-selector replay then includes the complete12-control run in its omitted-selector case; no second redundant complete12-case replay is needed on an unchanged tree. Empty/malformed selectors are tested through the production wrapper, not a copied predicate. The explicit-bound-empty M1R5 boundary is checked through PSBoundParameters, and the same-predicate/static-consumption boundaries are checked against the actual Fits definition. No broad gate or public mutation acceptance is claimed; those remain root-owned final-capstone obligations.

## Independent source review before executable checks

The normalization worker independently reviewed the two control sources against this frozen contract, read-only and without a build. It found no predicate/selector bypass or fixture mismatch in this scope. Its reconstruction confirmed all12 fixture names/order, unchanged Source program/entry/budget for the three supplied-memory mutants, rejection of the same packetOK(originalLiteral), exact per-cell provenance, preservation of the raw cell's quotient by2, the exact empty-memory transition/receipt/fault, actual Instruction.encoding/Fits equivalence, and the separate weaker executedFit observation. It also confirmed that all8 selector cases launch the production wrapper, bound-empty values cannot dispatch the full suite, successful output pins the exact selected PASS-name order, and the wrapper preserves the source import closure while honestly recording the pre-existing dirty shared baseline. The subsequent Lean and executable replay checks independently passed as recorded below.

## Exact propositions and object composition

The checked expected-type example is universally quantified over the supplied memory, code, fuel and entry state:

```lean
example (memory : Memory) (code : Program) (fuel : Nat) (state : State) :
    runArray memory code.toArray fuel state = run memory code fuel state :=
  runArray_toArray memory code fuel state
```

Each baseline and supplied-memory mutant executes the literal object chain `Allocation.memory [false]` (or its single `List.set` copy) -> `PackedBitvector.program operation` -> `code.toArray` -> `runArray`, using `(PackedBitvector.source operation).size + 1` fuel and `PackedBitvector.initial operation false argument`. No reference answer enters that execution. The literal expected packets are fixed in the registry before execution and checked at three result projections: `actual.result = some packet`, `actual.final.status = halted packet`, and the operation's actual result register equals that packet. The enclosing receipt record alone cannot satisfy this predicate.

For each successful read, `readsBacked` checks its actual reply against `suppliedMemory[receipt.address]?`; the mutation also requires a receipt of the exact changed address/value in both the baseline and mutant runs. This is a finite operational witness with a value-level difference, not a universal claim about all corruptions or a synthetic replay trace. The empty-memory fixture retains its exact transition index and receipt; it does not replace occurrence identity with source-label membership.

The exact static acceptance predicate is `P width code := ∀ instruction ∈ code, instruction.Fits width`. The reflected checker traverses `Instruction.encoding`, and the following independently stated propositions are proved:

```lean
instructionFitsB width instruction = true ↔ instruction.Fits width
programFitsB width code = true ↔ ∀ instruction ∈ code, instruction.Fits width
¬ (∀ instruction ∈ PackedBitvector.program operation ++ [.constant 0 (2 ^ width)],
  instruction.Fits width)
```

The rejection theorem holds for every operation and width, and rejects the actual encoded oversized operand by irreflexivity of `<`. Its predicate is exactly the baseline's whole-program predicate. The runtime `executedFit` observation quantifies only over reached transitions and is deliberately recorded separately: the dormant control shows why it cannot substitute for whole-program width coverage. The original canonical programs are unaffected. The appended supplied program gets one additional unit of fuel; its actual observed steps, ordered reads and returned packet remain equal to the canonical run.

The raw-bit amendment also has a checked arithmetic proposition: for every natural `value`, `value % 2 = 0` implies `(value + 1) / 2 = value / 2 ∧ (value + 1) % 2 = 1`. The runtime fixture separately checks the original cell exists, is even, and satisfies those same quotient/remainder properties after replacement. Thus the exact recorded large cell values do not erase adjacent packed fields.

These controls discharge the assigned finite instances of store identity, value dependency, read backing, execution-derived trace, independent expected values, validation reach, instruction/address-width rejection, and mutation reproducibility. All-size machine correctness, public space/execution composition and public-certificate anti-bypass mutations are separate root-owned capstone obligations; these finite controls do not purport to prove them.

## Replay and command ledger

Run from the repository root on Windows with the pinned Lean4.22.0 installation. The wrapper defaults to a fresh timestamp/GUID tag on every invocation, so previously committed evidence cannot suppress a replay:

```powershell
pwsh -NoProfile -File scripts/packed_bitvector_machine_controls.ps1 -Startup
pwsh -NoProfile -File scripts/packed_bitvector_machine_controls.ps1 -Case access-raw-cell
pwsh -NoProfile -File scripts/packed_bitvector_machine_controls.ps1 -ReplaySelectors
```

The final command includes the full12-control run through the omitted selector. It also starts the actual production wrapper for all seven other selector cases. An explicitly supplied empty string is recognized through `PSBoundParameters.ContainsKey('Case')` and rejected before semantic execution. Whitespace, malformed, unknown and padded values likewise fail, as does combining a case with another mode. Exact selected PASS-name order/count and summary are checked independently of the Lean fixture's internal return code.

| Stage and role | Coverage and distinct purpose | Observed outcome and bound |
| --- | --- | --- |
| [controller-machine-startup-r16](commands/controller-machine-startup-r16.json), development prerequisite | MC-TRUST, startup/registry shape and expected-type proofs before executable campaign; direct pinned `lake env lean --run ... --startup`. | PASS23.7s, deadline180s. Four printed inventories use only standard axioms; no Lean warnings/errors. |
| [controller-machine-known-r17](commands/controller-machine-known-r17.json), development prerequisite | MC-MEMORY/REPLAY; production wrapper with the single known access-raw-cell selector, establishing executable startup and exact raw-cell behavior before full replay. | PASS31.695s, outer deadline240s/Lean180s. This observed runtime informed the final campaign margin. |
| [controller-machine-selectors-r18](commands/controller-machine-selectors-r18.json), final required | MC-MEMORY/FAULT/STATIC/REGISTRY/REPLAY; one complete12-control omitted run plus exact eight-selector production campaign. | PASS103.51s, outer deadline600s/Lean180s/selector child240s. No retries, timeouts, output limits or source changes. |
| [controller-machine-static-r20](commands/controller-machine-static-r20.json), final required | MC-TRUST/REPLAY; whole-RMQ plus owned-Lean trust/native scans, PowerShell parser, working-tree and exact-base committed-range whitespace, source hashes and frozen-matrix integrity. | PASS; the two negative scans have no matches. Existing Git CRLF/global-ignore warnings are recorded separately from semantic verification. |

Exact production evidence: [known case](commands/machine-controls-v1-20260912111911796-bcf37cc6.json), [eight-selector replay](commands/machine-controls-v1-20260912111955043-999b380b.json), [all12 omitted cases](commands/machine-controls-v1-20260912111955043-999b380b-omitted.json), and [valid selector](commands/machine-controls-v1-20260912111955043-999b380b-valid.json). The outer replay records invalid cases even though their production child correctly rejects before creating an inner semantic-run record. It began2026-09-12T11:19:57Z and finished11:21:32Z at HEAD645a0502b9da9ad6444edbe44759e1c2c5661f25 plus the recorded shared working changes. Every before/after source hash is retained;134 local import/control/runner/toolchain files are covered. The frozen acceptance matrix remains SHA256 `80BD59A314FD33D37076802954444DA24F65C87A2A91DE23BC668B6AF9CCEB24`.

The exact selector exits were0,0,2,2,2,2,2,2 in the frozen order. Each child reports Windows `kill-on-close-job` ownership and no timeout. This leaf adds no cross-platform cleanup claim; it uses the existing Windows owned-process helper. The evidence explicitly says `baselineWasGloballyClean=false`, because sibling work was already present. `exactRestoration=true`, `scopedStatusRestored=true` and `whitespaceCheck=true` concern the immutable source closure, not an invented claim that the shared repository started clean.

There was no executable edit after these passing runs. Completing this evidence report only changes prose and does not invalidate the checked import closure. No standalone duplicate all12 replay, broad build or aggregate gate was run: the assigned finite campaign is covered once by r18, while root owns final integration/design-policy/public-certificate checks on the composed capstone tree. No separate machine design was introduced; the only fixture amendment preserves the actual packed cell, and root owns the branch design/process ledger.

## Proof digestion

Conceptually, these controls connect three kinds of rejection to the actual machine. Changing a charged data cell changes the returned value; removing all supplied memory produces the first real load failure; and adding an unreachable oversized operand breaks whole-program width coverage even though the executed path still succeeds. Their expected values are literal and their positive/negative cases use the same predicates, so passing the campaign cannot be achieved merely by changing a log or by silently substituting a stronger rejection condition.

The live assumptions are the existing primitive machine interpreter, array/list-run bridge, actual Source/Allocation definitions and the pinned Windows/Lean execution environment. The four local proofs use only the standard project axiom set. The observed12-case campaign is finite executable evidence; all-size source, safety and canonical memory theorems are the previously checked separate leaves consumed by the parent capstone. A skeptical grad student can now replay these exact fixtures and inspect the actual result projections and width predicate, then inspect the parent's universal public-composition theorem and its separate proposition-mutation consumer campaign for the broader claim. No assigned machine-control row remains open.

The initial static-evidence serialization attempt r19 was interrupted in its owned session after PowerShell tried to serialize rich Git warning objects. The corrected r20 recording converts external output to plain strings and passed all seven checks. No Lean or full executable campaign was rerun for this evidence-format repair.
