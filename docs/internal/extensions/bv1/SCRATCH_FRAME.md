# BV-1 actual finite scratch bank

Status: CANDIDATE_COMPLETE for this leaf only. Frozen before source edits under governance
`0e6a00f654abc64f8b68988fa9675b9a839dca2f`, continuation checkpoint
`645a0502b9da9ad6444edbe44759e1c2c5661f25`, and the canonical proof-sprint gate.
This worker owns `ScratchFrame.lean`, this evidence and its exact consumer only.
Other workers' edits and the inherited OPEN BV-1 matrix are preserved.

## Frozen requirement and target

Verbatim assignment: "Complete capacity counts8271 registers+pc/status/result,
so prove actual program of each operation writes only registers<8271 and hence
for EVERY fuel prefix, every r≥8271 stays0 from actual initial state. Use actual
source writes scopes (Packed RankWrites,SelectWrites, NumericReader and
accessQuery) and generic additive compiler/primitive frame helpers; no shared
Packed edits."

The exact counted bank is `Space.registerCount`, defined in the actual namespace
as `RMQ.PackedBitvector.registerCount = 8271`; scratchWords is registerCount+3.
Freeze `source_writes_registerBank operation` with conclusion
`(source operation).WritesOnly (fun r => r < registerCount)` and
`program_writes_registerBank operation` with conclusion
`∀ instruction ∈ program operation, instruction.WritesOnly
  (fun r => r < registerCount)`.
The final all-prefix conclusion, for arbitrary memory, operation, target,
argument, fuel and register with `registerCount ≤ r`, is exactly
`(run memory (program operation) fuel (initial operation target argument)).final.regs r = 0`.
`execute_finite_registers` specializes the same theorem to the canonical memory
and actual operation fuel. No fit or valid-argument premise is needed.

| ID | Requirement | Consumer and exact composition | Challenge | Status |
| --- | --- | --- | --- | --- |
| SF-WRITES | actual program of each operation writes only registers<8271 | actual source write scopes → existing Block.compile_writesOnly → program including final halt | All three operations and actual physical reader included | CANDIDATE_COMPLETE |
| SF-PREFIX | for EVERY fuel prefix, every r≥8271 stays0 from actual initial state | program write theorem → existing primitive run_frame → actual initial registers → canonical execute | Arbitrary memory/fuel includes faults and halted suffixes; high argument may be unrepresentable without changing support | CANDIDATE_COMPLETE |
| SF-COUNT | Complete capacity counts8271 registers+pc/status/result | All conclusions use exact registerCount from Space, not a separately chosen bank | Exact type consumer pins counted constant and actual programs | CANDIDATE_COMPLETE |
| SF-CHECK | no shared Packed edits | Narrow owned check/typed consumer/axioms and hygiene after explicit build slot grant | No overlap or aggregate; inherited matrix unchanged | CANDIDATE_COMPLETE |

A same-predicate kernel counterexample rejects an operation-family program
that writes a nonzero constant exactly at the first excluded register. This
checks support, not merely register-value fit. No mutation campaign or public
capstone completion is claimed by this leaf.

Verification: direct pinned v4.22.0 Lake through run_command.ps1, initial warm
180-second deadline and unique stages, then exact imported consumer plus axiom
reports and whitespace/trust scans. No broad build. Root owns commits and
integration.

## Checked evidence and digestion

The checked source is 4,640 bytes, SHA-256
`0EB35B270F66D55C250D9EF6DC46D897F7AFD1AA8E07D5EA40A6EB2D7784905A`.
Source remained unchanged after the clean build.

The joint stage `canonical-select-safety-1` gave an ordinary 24.513-second
diagnostic: the literal setup range required explicit List.range_succ expansion
for its write scope. All remaining scratch-frame proofs, including the negative
control, passed that diagnostic. Joint stage `canonical-select-safety-2` passed
in 21.295 seconds with no local warnings. The independent imported stage
`scratch-frame-consumer-1` passed in 6.825 seconds, with seven expected-type
propositions and six axiom reports. Reports use only `propext`, `Classical.choice`,
`Quot.sound`; the negative control uses only `propext`, `Quot.sound`.
Exact invocations and owned results are in `commands/<stage>.json`. The direct
pinned v4.22.0 binary avoids the elan shim's earlier network attempt. All checks
ran with a 180-second deadline in the explicitly granted single-process slot;
release was announced immediately after the final consumer. No aggregate was
run. Both required repository trust scans returned no matches, and whitespace
checks passed, including explicit checks for these untracked source files.

The change connects existing source write scopes to the actual compiler output,
then connects the primitive register-frame theorem to the real initialized
register function. In plain English, execution can retain nonzero register data
only in the 8271 cells already charged by Space, even when supplied arbitrary
memory, arbitrary arguments and arbitrary fuel. This supplies finite support,
which numerical Fits bounds alone do not provide. The three additional counted
cells for program counter, status and result remain the existing Space model.
No input, shape, fit, termination or memory-validity hypothesis is live.

The negative control proves
`¬ PreservesScratchBank (fun _ => [.constant registerCount 1])` using the same
all-memory/all-operation/all-argument/all-fuel predicate as the positive theorem.
At memory=[], operation=access, target=false, argument=0, fuel=1, the first
excluded register becomes 1. It does not merely fail a weaker numerical bound.
No mutation campaign is claimed. The numeric-reader worker independently read
this exact source/compiler/run/initial-state chain and reported no scope or
object-identity gap; no separate build was run by that reviewer.

A skeptical reader should next check the separate value-fit, code-size and
capacity joins use this exact registerCount and actual programs. This leaf
supplies support only; it does not change the abstract register representation,
claim runtime allocation behavior, or close whole BV-1 acceptance. The parent
owns those joins and the final capstone. This proves the approved scratch-bank
accounting decision without changing it; no design/process ledger or shared
Packed source was edited, and no commit was made.

## Exact checked external consumer

```lean
import RMQ.Core.WordRAM.Bitvector.ScratchFrame
open RMQ RMQ.PackedBitvector
open RMQ.SuccinctFinal.PackedWordRAM RMQ.SuccinctFinal.PackedWordRAM.Structured
namespace BV1ScratchConsumer
example (operation : Operation) : (source operation).WritesOnly (fun r => r < 8271) :=
  source_writes_registerBank operation
example (operation : Operation) : ∀ instruction ∈ program operation,
    instruction.WritesOnly (fun r => r < 8271) := program_writes_registerBank operation
example (memory : Memory) (operation : Operation) (target : Bool)
    (argument fuel r : Nat) (hr : 8271 ≤ r) :
    (run memory (program operation) fuel (initial operation target argument)).final.regs r = 0 :=
  run_finite_registers memory operation target argument fuel r hr
example (bits : List Bool) (operation : Operation) (target : Bool)
    (argument r : Nat) (hr : 8271 ≤ r) :
    (execute bits operation target argument).final.regs r = 0 :=
  execute_finite_registers bits operation target argument r hr
example : scratchWords = 8274 := rfl
example : ∀ memory operation target argument fuel r, 8271 ≤ r →
    (run memory (program operation) fuel (initial operation target argument)).final.regs r = 0 :=
  program_preservesScratchBank
example : ¬ (∀ memory operation target argument fuel r, 8271 ≤ r →
    (run memory [.constant 8271 1] fuel (initial operation target argument)).final.regs r = 0) :=
  outOfBankWrite_rejected
#print axioms source_writes_registerBank
#print axioms program_writes_registerBank
#print axioms run_finite_registers
#print axioms execute_finite_registers
#print axioms program_preservesScratchBank
#print axioms outOfBankWrite_rejected
end BV1ScratchConsumer
```
