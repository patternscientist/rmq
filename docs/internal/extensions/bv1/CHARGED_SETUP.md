# BV-1 charged setup — frozen leaf contract

Owner: numeric_reader. Parent assignment at checkpoint
`645a0502b9da9ad6444edbe44759e1c2c5661f25`, governance
`0e6a00f654abc64f8b68988fa9675b9a839dca2f`. Exact project skill preflight
passes again with required rmq-proof-sprint and the three actually exposed RMQ
skills. Scope is new ChargedSetup.lean, its embedded exact consumers, and this
record. Parent owns Source, Allocation, controller joins and shared ledgers.
The other three agents have disjoint proof leaves; no additional subagent
would shorten this small sequential setup proof. No Lean runs before the
parent grants the build slot.

## Verbatim assigned requirements

CS-EXEC: "Prove the ACTUAL Experiment.setup and targetSetup execute over
Allocation.memory bits with exact loaded metadata, exact successful load
receipts, preserved argument/target registers, and source Safe from explicit
numerical entry-fit/memory-fit hypotheses (no uncharged setup oracle)."

CS-META: "Source.lean runs setup then operationBody; Allocation.scalarHeader
has 23 cells; setup maps first19 to regs16..34, targetSetup true replaces16
with17 and28..31 by cells19..22."

CS-CONSUMER: "Prefer canonical metadata function defined from actual
scalarHeader and initial input registers, plus final registers equality/frame
so root can instantiate Controller.MetadataMatches; no dependencies on
upcoming FinalReader."

CS-SAFE: "Actual all-size scalar bounds may be hypotheses in this leaf, but
setup addresses/constants must be explicitly safe from W>=32 and
MemoryWordsFit."

CS-CHECK: "Continue through narrow repairs/consumer and record proof
digestion; whole capstone remains root responsibility."

## Frozen expected interfaces before source edits

All declarations below are in RMQ.PackedBitvector.ChargedSetup, using the
existing Structured evaluator and safety predicate. Metadata is proof-side
description of the actual loaded values, never used by the executable setup.

```lean
def setupMetadata (bits : List Bool) (regs : Registers) : Registers :=
  fun r => if r = 6 then 18
    else if 16 ≤ r ∧ r < 35 then
      ((Allocation.scalarHeader bits)[r - 16]?).getD 0
    else regs r

def targetMetadata (bits : List Bool) (regs : Registers) : Registers :=
  fun r => if regs 3 = 0 then regs r
    else if r = 6 then 22
    else if r = 16 then regs 17
    else if 28 ≤ r ∧ r < 32 then
      ((Allocation.scalarHeader bits)[r - 9]?).getD 0
    else regs r

def setupReceipts (bits : List Bool) : List Receipt :=
  (List.range 19).map fun i =>
    ⟨i, some (((Allocation.scalarHeader bits)[i]?).getD 0)⟩

def targetReceipts (bits : List Bool) (regs : Registers) : List Receipt :=
  if regs 3 = 0 then [] else
    (List.range 4).map fun i =>
      ⟨19 + i, some (((Allocation.scalarHeader bits)[19 + i]?).getD 0)⟩

theorem setup_source (bits : List Bool) (regs : Registers) :
  Experiment.setup.eval (Allocation.memory bits) ⟨regs, .running⟩ =
    ⟨⟨setupMetadata bits regs, .running⟩, setupReceipts bits⟩

theorem targetSetup_source (bits : List Bool) (regs : Registers) :
  Experiment.targetSetup.eval (Allocation.memory bits) ⟨regs, .running⟩ =
    ⟨⟨targetMetadata bits regs, .running⟩, targetReceipts bits regs⟩

theorem setup_safe (bits : List Bool) (width : Nat) (regs : Registers)
  (hw : 32 ≤ width) (memoryFit : MemoryWordsFit (Allocation.memory bits) width)
  (fit : (⟨regs, .running⟩ : Data).Fits width) :
  Experiment.setup.Safe (Allocation.memory bits) width ⟨regs, .running⟩

theorem targetSetup_safe (bits : List Bool) (width : Nat) (regs : Registers)
  (hw : 32 ≤ width) (memoryFit : MemoryWordsFit (Allocation.memory bits) width)
  (fit : (⟨regs, .running⟩ : Data).Fits width) :
  Experiment.targetSetup.Safe (Allocation.memory bits) width ⟨regs, .running⟩
```

The exact-type consumer must combine setup then targetSetup, with final
registers `targetMetadata bits (setupMetadata bits regs)` and receipts
`setupReceipts bits ++ targetReceipts bits (setupMetadata bits regs)`, on the
same actual allocation. A second consumer must consume both safety theorems
on that actual sequential evaluation. Frame corollaries preserve every
register outside `{6} ∪ [16,35)`, including target register 3 and argument
registers 352, 512 and 704. Root can rewrite complete final registers to these
metadata functions and derive Controller.MetadataMatches pointwise.

| ID | Exact proposition / object chain | Anti-vacuity challenge | Status |
| --- | --- | --- | --- |
| CS-EXEC | Both exact Evaluation equalities above constrain status, all registers and every ordered successful receipt on Allocation.memory. | Changing any loaded scalar changes its destination projection; receipt-only disagreement is insufficient. | FROZEN |
| CS-META | setupMetadata and targetMetadata have the exact register/header maps above; scalar lookups are proved against Allocation.memory. | Address 18 is the last initial setup load; target true reads exactly addresses 19 through 22, while target false reads none. | FROZEN |
| CS-CONSUMER | Actual sequential evaluation consumes setup_source then targetSetup_source; same final metadata feeds the root controller interface. | Arbitrary argument registers survive unchanged, including registers 352/512/704; target branch follows actual register 3. | FROZEN |
| CS-SAFE | Both actual Block.Safe conclusions above use only explicit entry fit, memory-word fit and width at least 32. | Bound address 22 and every constant even though the allocation contains those cells; no host-array bound substitutes for machine fit. | FROZEN |
| CS-CHECK | Narrow owned target and embedded expected-type consumers; exact axiom inventories, trust/diff scans, command records and digestion. | No helper-only completion, no sibling executable or synthetic trace. | FROZEN |

Relevant inherited contributions are INV-STORE-IDENTITY,
INV-VALUE-DEPENDENCY, INV-TRACE-EXECUTION, INV-READ-BACKING,
INV-WORD-WIDTH, INV-ADDRESS-WIDTH, INV-PROOF-SEPARATION and INV-NO-SYNTHETIC.
The whole-client frozen matrix is untouched and remains root-owned. Static
instruction fields and compiled PC/transition obligations are separate root
compiler premises; source safety here is not their substitute. Broad gates,
public claims and full client acceptance are reserved for root integration.

## Evidence and digestion

Pending implementation. No build has been launched for this new leaf.

### Checked result

All four frozen theorem types close unchanged. The same-source sequential
consumers `setup_then_target_source` and `setup_then_target_safe` also close.
The external `charged_setup_expected_type.lean` independently pins both
individual Evaluation equalities and a conjunction of the composed exact
Evaluation with both individual Safe propositions and the composed Safe
proposition. Its frame example instantiates preservation at actual target and
argument registers 3, 352, 512 and 704.

| Stage | Command / change | Deadline | Duration | Outcome |
| --- | --- | --- | --- | --- |
| charged-setup-build-v1 | Initial launcher supplied the two Lake arguments as one comma-containing string. | 180 s | 1.468 s | Exit 1 before Lean; corrected by passing an actual PowerShell argument array. |
| charged-setup-build-v2 | pinned Lake `build RMQ.Core.WordRAM.Bitvector.ChargedSetup` | 180 s | 11.086 s | Exit 1; both individual Safe theorems passed. Four semantic normalization errors remained. |
| charged-setup-build-v3 | Same narrow target after qualifying shared primitive execute and removing a redundant range rewrite. | 180 s | 9.006 s | Exit 1; remaining map-append and inactive-branch function equalities. |
| charged-setup-build-v4 | Same narrow target after the two local equality repairs. | 180 s | 8.887 s | Exit 0; one unused simp hint. |
| charged-setup-build-final | Same narrow target after deleting the unused hint. | 180 s | 15.044 s | Exit 0; zero ChargedSetup warnings. |
| charged-setup-consumer-final | pinned Lake `env lean docs/internal/extensions/bv1/charged_setup_expected_type.lean` | 90 s | 6.853 s | Exit 0; independent expected-type consumer passes with no warnings. |

Every stage has its complete command/tree/source-hash/output/ownership record
under `commands/<stage>.json`. No stage timed out or exceeded its output cap.
The final stages had empty stderr and no terminated or surviving owned child.
Lean 4.22.0 and LEAN_NUM_THREADS=1 were explicit. The parent received a build
slot release immediately after the clean external consumer; no further Lean
run was launched for this leaf. The emitted ChargedSetup artifact is 697,800
bytes. Unchanged baseline import warnings are unrelated replayed diagnostics.

Final ChargedSetup.lean SHA256:
`21440D54C844202F5AF6816C5BFD1DFBE07EFA18ED23A7C546F8BF29948476E9`.
Final external consumer SHA256:
`5CCC0D63D945734387F6E8DDB4A9AD6D10F39A2EEDBD285DA48C46D5ACD2FB86`.
No source edit followed the final module check. All six printed source/safety
inventories and the external `charged_setup_required` inventory are exactly
`[propext, Classical.choice, Quot.sound]`. Prohibited-token, native_decide /
Lean.ofReduceBool, direct trailing-whitespace and conflict-marker scans over
both owned Lean files are empty. `git diff --check` passes with only existing
LF/CRLF advisories. The full inherited matrix remains unchanged at SHA256
`80BD59A314FD33D37076802954444DA24F65C87A2A91DE23BC668B6AF9CCEB24`.

### Requirement reconstruction

CS-EXEC and CS-META: `memory_scalar` proves, for every index below 23,
`(Allocation.memory bits)[index]? = some
(((Allocation.scalarHeader bits)[index]?).getD 0)`. It peels actual allocation
prefixes and uses the checked scalar-header length. `prefix_source` then
induces over the actual setup's mapped load pairs, recording each successful
load and updating the corresponding destination. Its count-19 instance is
exactly the frozen `setup_source` Evaluation equality. `targetSetup_source`
uses the actual register-3 branch, the actual move from 17 to 16, and the four
actual successful allocation lookups. Neither proof substitutes an execution,
computes a semantic answer before loading, or adds decorative receipts.

CS-CONSUMER: `setup_then_target_source` rewrites the actual Structured sequence
using the two frozen equalities, so it identifies one final register function,
running status, and the exact concatenated receipt sequence. The direct frame
theorems preserve every `r ≠ 6` with `r < 16 ∨ 35 ≤ r`; the external consumer
checks target and all three argument registers. Root may instantiate
Controller.MetadataMatches by rewriting this full final-register equality.
No upcoming reader module is imported or assumed.

CS-SAFE: setup_safe and targetSetup_safe have only the frozen explicit fit
premises. They construct safety of actual source actions, with constant
addresses below the proved `2^32 ≤ 2^width` capacity. Every load uses
MemoryWordsFit.reply; every move uses the actual state's fit invariant.
Block.eval_fits transports that invariant between successive source actions.
The composed safety consumer evaluates the real initial setup to choose its
second starting state. It does not merely prove final-register fit.

The checked boundary cases are constructor/range branches within these
universal proofs: scalar index 18 is included in the setup range; target zero
leaves registers unchanged and has no target receipts; every nonzero target
loads exactly 19, 20, 21, 22; arbitrary original registers outside the write
range survive. Each packet-free metadata destination equality and receipt is
fixed by the source equalities. No mutation campaign or runtime benchmark is
claimed for these proof branches.

### Proof digestion and disposition

The machine now has a checked bridge from charged numerical header loads to
the controller's proof-side metadata view. The view describes the loaded
registers; executable setup never calls it. Both target branches and all
original inputs are covered, and the same proof composes to source safety.
The only live safety assumptions are width at least 32, input-register fit,
and word fit of the exact supplied allocation. Semantic setup correctness is
unconditional for every bitvector and initial register function.

A skeptical graduate student should next ask whether the canonical allocation
proves memory-word fit at the chosen width, whether the controller uses this
exact loaded metadata, and whether the compiler carries this source execution
to charged primitive transitions with static fields and PC bounds. Those are
root integration obligations. No full-client result, source-cost primitive,
new representation choice, commit, push or broad gate is asserted here.
Root owns design/public ledgers and final certification; this leaf made only
routine proof decomposition choices.

Leaf status: `CANDIDATE_COMPLETE`, pending coordinator reconstruction. All
CS-EXEC, CS-META, CS-CONSUMER, CS-SAFE and CS-CHECK leaf rows have the checked
evidence above; whole-client inherited rows remain untouched.
