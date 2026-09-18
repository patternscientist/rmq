# BV-1 canonical access/rank safety — frozen leaf contract

Owner: numeric_reader. Same exact BV-1 checkpoint/governance and unchanged
frozen whole-client matrix as preceding owned leaves. Canonical proof-sprint
skill preflight passed on this continued task. Scope: new
CanonicalRankAccessSafety.lean, this report and an independent exact-type
consumer. Root owns Source, semantic operation/API joins and Observations;
normalization owns CanonicalSelectSafety and its all-operation canonical safety
prerequisites. No Source/shared Packed/peer edits and no Lean before explicit
build-slot grant. All four agents have disjoint necessary joins; this proof
depends sequentially on the canonical safety interfaces and needs no further
subagent.

## Verbatim target and frozen propositions

CRAS-ACCESS: "canonical_access_source_safe/canonical_access_execution_safe for
actual source/program .access and initial .access false arg".

CRAS-RANK: "canonical_rank_source_safe/canonical_rank_execution_safe for actual
.rank both targets; sole hypothesis arg<2^W."

CRAS-CONSUME: "Consume your accessQuery_safe for access; for rank actual
rankQuery prepare/check + Controller.rankBlock_safe_bound, adding1 only on
valid branch (envelope+1 fits from SafetyLimits.square or semantic output≤n)."

CRAS-EXACT: "Freeze exact whole-source/actual compiled all-prefix/transition/
backing targets before edits; no extra readiness/geometry premises."

The four exported endpoints are in RMQ.PackedBitvector, with these exact types:

```lean
theorem canonical_access_source_safe (bits : List Bool) (argument : Nat)
  (ha : argument < 2 ^ Experiment.width bits.length) :
  (source .access).Safe (Allocation.memory bits) (Experiment.width bits.length)
    ⟨(initial .access false argument).regs, .running⟩

theorem canonical_rank_source_safe (bits : List Bool) (target : Bool) (argument : Nat)
  (ha : argument < 2 ^ Experiment.width bits.length) :
  (source .rank).Safe (Allocation.memory bits) (Experiment.width bits.length)
    ⟨(initial .rank target argument).regs, .running⟩

theorem canonical_access_execution_safe (bits : List Bool) (argument : Nat)
  (ha : argument < 2 ^ Experiment.width bits.length) :
  RankExecutionSafety (Allocation.memory bits) (Experiment.width bits.length)
    (program .access) ((source .access).size + 1) (initial .access false argument)

theorem canonical_rank_execution_safe (bits : List Bool) (target : Bool) (argument : Nat)
  (ha : argument < 2 ^ Experiment.width bits.length) :
  RankExecutionSafety (Allocation.memory bits) (Experiment.width bits.length)
    (program .rank) ((source .rank).size + 1) (initial .rank target argument)
```

RankExecutionSafety is the existing generic compiled-run observation
conjunction, reused at these actual operation sources/programs. The independent
consumer must expand it for each of the two operations. Specifically, for
`operation = .access, target = false` and for `.rank` with either target, let
`actual := execute bits operation target argument`; its exact conclusion is:

```lean
(∀ instruction ∈ program operation, instruction.Fits (Experiment.width bits.length)) ∧
actual.final.Fits (Experiment.width bits.length) ∧
(∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
  Instruction.Safe (Experiment.width bits.length) t.before t.instruction ∧
    t.after.Fits (Experiment.width bits.length)) ∧
(∀ index, index ≤ (source operation).size + 1 →
  (run (Allocation.memory bits) (program operation) index
    (initial operation target argument)).final.Fits (Experiment.width bits.length)) ∧
(∀ (index : Nat) (t : Transition) (receipt : Receipt),
  actual.transitions[index]? = some t → t.receipt = some receipt →
  receipt.address < 2 ^ Experiment.width bits.length ∧
  receipt.reply = (Allocation.memory bits)[receipt.address]? ∧
  (∀ value, receipt.reply = some value → value < 2 ^ Experiment.width bits.length))
```

The final source/execution types introduce no memory-fit, metadata, reader,
shape, readiness or numerical-envelope hypotheses. Those are proved internally
from initial_data_fits, actual charged setup, loadedModel_safetyBounds,
loadedModel_readerSafe and the canonical allocation. The source-safe access
proof must consume AccessProof.accessQuery_safe. The rank proof must consume
the existing Controller.rankBlock_safe_bound at the actual rankPrepare output;
any stopped branch remains stopped, and the valid running branch's packet
increment must be safe.

| ID | Exact evidence / object chain | Anti-vacuity boundary | Status |
| --- | --- | --- | --- |
| CRAS-ACCESS | First and third frozen propositions checked verbatim by actual_access_source_required / actual_access_execution_required. Same initial/source/program/Allocation.memory; rank_compiled_safety preserves the source judgment. | The checked universal type retains empty bits and every representable index ≥ n; no successful-query premise removes the actual invalid branch. | CANDIDATE_COMPLETE |
| CRAS-RANK | Second and fourth frozen propositions checked verbatim by actual_rank_source_required / actual_rank_execution_required for both Bool targets. | The checked universal type retains endpoint n and representable n+1. Source comparison selects the same body/skip arms; the increment is checked in its actual selected body. | CANDIDATE_COMPLETE |
| CRAS-CONSUME | ChargedSetup.setup_safe and setup_source → actual setupMetadata → loadedModel_readerSafe / loadedModel_safetyBounds → accessQuery_safe or rankBlock_safe_bound after actual rankPrepare → source Safe. | External consumer types contain only argument fit; no metadata, memory, reader or readiness premise was introduced. | CANDIDATE_COMPLETE |
| CRAS-EXACT | External consumer expands all five frozen instruction/final/transition/prefix/receipt-backing conjuncts on execute; PASS 7.450 seconds. | A final-fit-only conclusion or receipt list from a sibling run does not match the independently written required proposition. No mutation campaign is claimed. | CANDIDATE_COMPLETE |

Relevant inherited rows include INV-STORE-IDENTITY, INV-WORD-WIDTH,
INV-ADDRESS-WIDTH, INV-INSTRUCTION-ATOMICITY, INV-ALL-SIZE,
INV-TRACE-EXECUTION, INV-READ-BACKING and INV-PUBLIC-COMPOSITION. These are
contributions to root's whole-client join, not edits to frozen matrix rows.
Semantic value/exact ordered receipt theorems, charged complete capacity,
outer API guards and final public claims remain root-owned.

Verification: inventory prerequisite artifacts; no build while canonical
dependencies remain pending. Once granted, run the exact warm module with a
180-second owned deadline, then independent expected-type consumer and exact
axiom inventories. Repair local failures narrowly; record all stages. Own
trust/direct whitespace/conflict scans and git diff --check are required.
Root reserves aggregate gates/design/public certification for integration.

## Evidence and digestion

Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

The four frozen endpoint types above are unchanged. The source module also
exports canonical_access_source_fieldsFit and canonical_rank_source_fieldsFit.
These cover every fixed source instruction, including dormant arms, with
literal register/operand capacity derived from W >= 32. The compiler theorem
additionally covers encoded branch destinations, the halt instruction and
every executed program counter, using Observations.source_budget: 132 steps
for access and 1450 for rank. They are upper bounds on actual executed steps,
not a claim that every query consumes the complete fuel.

The actual object chain is:

1. The sole argument-fit hypothesis establishes all initial data fit through
   initial_data_fits. ChargedSetup.setup_safe checks the actual nineteen loads
   against canonical_memoryWordsFit on Allocation.memory bits.
2. ChargedSetup.setup_source rewrites the actual setup evaluation to its
   loaded register function. The access metadata constructor establishes
   target 0, size n, M = machineWordBits n, and W. The access source uses
   AccessProof.accessQuery_safe and loadedModel_readerSafe directly.
3. Rank executes its actual guard and seven-instruction rankPrepare. The
   local rankPrepare_source theorem identifies the complete evaluated
   register function, whose low metadata are unchanged. It installs n, M,
   blocksPerSuper = M, segment IDs 17/18/19 and the target register.
   Controller.rankBlock_safe_bound receives the canonical reader simulation,
   ReaderSafe, actual physicalReader writes, controller bounds and the
   segment-19 raw-length theorem. Its actual output register 360 is bounded
   by the canonical envelope. The actual final addition is safe because
   envelope + 1 < 2^W, derived from SafetyLimits.square and envelope_pos.
   A stopped evaluation remains supported by Block.safe_stopped.
4. The same source Safe and FieldsFit proofs feed rank_compiled_safety at
   the actual program, initial state, Allocation.memory and source.size+1.
   The independent consumer restates all five observations using the actual
   execute expression; its proof uses only the matching canonical endpoint.

No new executable source, copied reader/controller, alternate run, proof-only
setup oracle or additional caller-side readiness premise was introduced.
There is no CartesianShape assumption in these endpoint types. The generic
compiler and reused proof dependencies retain the established Lean/Std trust
base; no native decision procedure or foreign implementation is used.

### Exact verification

All stages used the pinned Lean 4.22.0 toolchain, LEAN_NUM_THREADS=1 and the
owned kill-on-close process helper. Root granted the c974 build slot after
Observations passed. All imports were warm at the first run. Full output,
source hashes, command arguments, deadlines and process results are durable
in commands/<stage>.json.

| Stage | Exact result | Interpretation |
| --- | --- | --- |
| canonical-rank-access-safety-build-v1 | FAIL, exit 1, 18.187 seconds / 180 | Ordinary proof diagnostics: access apply goal order, width aliases, and one missing positive-width fact. No timeout. |
| canonical-rank-access-safety-build-v2 | FAIL, exit 1, 19.830 seconds / 180 | Access endpoints passed. One rank increment goal remained: width ≠ 0 and regs360+1 < 2^width. No timeout. |
| canonical-rank-access-safety-build-final | PASS, exit 0, 16.780 seconds / 180 | Four endpoint axiom inventories; zero own warnings. |
| canonical-rank-access-safety-consumer-final | PASS, exit 0, 7.450 seconds / 90 | Independent source and expanded actual-run consumers; four axiom inventories, zero warnings. |
| canonical-rank-access-safety-static-final | PASS | Full RMQ/lakefile forbidden-token scan and full RMQ native-decision scan found no matches; owned source/consumer conflict/debug/trust scan found no matches; git diff --check exit 0. |

Every final endpoint and independent consumer reports exactly
`[propext, Classical.choice, Quot.sound]`. Temporary failed elaborations in
the first two diagnostic records contain Lean's failed-proof marker; neither
record is acceptance evidence. Final compiled artifact:
`.lake/build/lib/lean/RMQ/Core/WordRAM/Bitvector/CanonicalRankAccessSafety.olean`,
1,255,720 bytes. No Lean source changed after the final successful module run.
The slot was released immediately after the successful consumer; no owned
process remains.

Exact checked source SHA256:
`1C39E9D0A2637C45B7306DBD5077DD2319BA2F6C2AF7CA43D0DE189F9BBAC03C`.
Exact consumer SHA256:
`09503EDC196B297B331C3ADDCC938D863D2568AA85C161D34A2EE7BB84221E71`.
The whole-client frozen matrix remains byte-identical at SHA256
`80BD59A314FD33D37076802954444DA24F65C87A2A91DE23BC668B6AF9CCEB24`.
The shared checkout remains at the assigned source HEAD
`645a0502b9da9ad6444edbe44759e1c2c5661f25`; these are uncommitted owned files
under root's explicit no-separate-commit instruction. Root owns final exact
commit, committed-range/design-policy checks and public aggregate gates.
The narrow module plus external consumer were proportionate for this leaf;
no full Lake/gate run was needed here.

### Proof digestion

Conceptually, this removes all internal safety assumptions from the access
and rank interfaces by proving them from the actual counted allocation and
the metadata loaded by charged setup. In plain English, every representable
query can execute the fixed access/rank code without overflowing its modeled
word, using an out-of-range instruction field or producing an unbacked read.
The result holds for empty inputs, invalid but representable indices and both
rank targets because those remain inside the checked universal types.

The live caller assumption is only argument < 2^W. The theorem uses the
existing numerical word-RAM source/compile/run semantics; it does not assert
native Lean runtime bounds. Semantic packets, exact ordered operation reads,
space joins and the natural-number API's outer representability guard remain
the explicitly root-owned final composition obligations.

A skeptical reader should trace the rank packet increment back to the actual
rankBlock evaluation and verify that the memory in the prefix/read-backing
conjuncts is Allocation.memory bits. Both links are present in the checked
source and independent consumer. They should next inspect root's final join
to ensure the already proved answer, space and safety conjuncts use this same
program/run. That is the separate whole-capstone contract, not an unresolved
condition in these four safety propositions.

No design or workflow model was changed: the leaf instantiates the existing
canonical allocation, controller bounds and compiler safety interface. No
new ADR or process decision was necessary within this disjoint write scope;
root owns the broader BV-1 architecture and public-surface synchronization.
