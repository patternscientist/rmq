Status: INCOMPLETE
Phase: FINITE_LEAF_CHECKED

This is the independently assigned finite-container leaf returned to the NATIVE-1 lead. The leaf's operation and whole-run simulation proofs check. It is not a report of full NATIVE-1 completion: the frozen matrix remains authoritative, and the native capstone, finite limb representation, serialization, source boundary, API, controls and coordinator acceptance are separate consumers still being assembled by the lead.

Worker identity: NATIVE-1 / finite_storage. Requested task title: `(NATIVE-1) Verify native packed execution`.

Base and governance: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Branch: `codex/native-1-packed-execution`.
Worktree: `C:/Users/poin/.codex/worktrees/1817/RMQ`.
HEAD at leaf verification: the base SHA above. No leaf commits were authorized; the lead owns staging and commits.
Owned paths: `RMQ/Core/WordRAM/Native/Finite.lean` and this note only.

The runtime RMQ catalog was exactly `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`. The canonical proof-sprint skill, completion gate, AGENTS.md, roadmap passage, Primitive/Scratch/ArrayRun and relevant design entries were read. Exact-governance preflight with `rmq-proof-sprint` required returned PASS, with no missing or stale names. The lead's frozen `ACCEPTANCE_MATRIX.md` existed and was read before the first proof edit.

## Checked object and proof chain

Namespace: `RMQ.SuccinctFinal.PackedNative`, with existing machine declarations in `PackedWordRAM`.

`FiniteState` contains `regs : Array Nat`, `pc : Nat`, and `status : Status`. Its read is `s.regs[r]?.getD 0`. `executeFinite` consumes `memory : Array Nat`; `stepFinite` and `runFinite` additionally consume `program : Array Instruction`. Thus all three indexed stores are actual arrays. Natural-number cells and operands are intentional intermediate representations, not bounded words or limbs.

`FiniteState.ofState capacity s` allocates `Array.ofFn (fun r : Fin capacity => s.regs r.val)`, retaining the exact pc and status. Its size is proved equal to `capacity`. `FiniteState.decode_ofState` has the checked type:

```lean
theorem FiniteState.decode_ofState (capacity : Nat) (s : State)
    (hzero : ∀ r, capacity ≤ r → s.regs r = 0) :
    (FiniteState.ofState capacity s).decode = s
```

`FiniteState.writeNext` uses `Array.setIfInBounds`, advances the pc once and sets running status. The guarded write simulation is:

```lean
theorem FiniteState.writeNext_decode (s : FiniteState) (dst value : Nat)
    (h : dst < s.regs.size) :
    (s.writeNext dst value).decode = s.decode.writeNext dst value
```

The omitted-register convention is explicit: for every `r` with `s.regs.size ≤ r`, `FiniteState.read_above` proves `s.read r = 0`. Source registers need not be bounded. Every destination does need to fit the bank. Outside this guard, `setIfInBounds` leaves the register bank alone; this leaf does not claim that this unsupported write agrees with the reference write. A checked API must enforce the destination support guard.

The constructor-exhaustive instruction theorem is:

```lean
theorem executeFinite_decode (memory : Array Nat) (i : Instruction) (s : FiniteState)
    (hwrites : i.WritesOnly (fun r => r < s.regs.size)) :
    ((executeFinite memory i s).1.decode, (executeFinite memory i s).2) =
      execute memory.toList i s.decode
```

The proof separately covers load, constant, move, arithmetic, comparison, jump, register jump, zero branch and halt. Arithmetic and comparison consume the exact existing `op.eval` definitions, so their operators are universally quantified, rather than restricted to fixtures. There is no new RMQ algorithm, decoding oracle, answer field, post-hoc load, or separately generated trace.

For a load, the finite evaluator computes the address from the current finite register bank and reads `memory[address]?`. The success branch writes that exact reply; the missing-cell branch sets fault and retains `some ⟨address, none⟩`. The theorem imposes no premise on cell contents or successful loading, so corrupt natural cells and missing cells remain within its quantified domain.

`executeFinite_size` proves that every instruction preserves `s.regs.size`, without even requiring the destination guard. `stepFinite_size` propagates that fact to an actual fetched transition. `stepFinite_decode` proves equality after mapping each actual finite transition through its decode, under destination bounds for every instruction in `program.toList`.

`FiniteTransition` retains its actual before-state, fetched instruction, after-state and optional receipt. Its decode retains all four fields. `FiniteRun.decode` retains the decoded final state and maps this transition decode over the ordered finite list. The full theorem is:

```lean
theorem runFinite_decode (memory : Array Nat) (program : Array Instruction)
    (fuel : Nat) (s : FiniteState)
    (hwrites : ∀ i ∈ program.toList, i.WritesOnly (fun r => r < s.regs.size)) :
    (runFinite memory program fuel s).decode =
      run memory.toList program.toList fuel s.decode
```

This is equality of whole `PackedWordRAM.Run` values, not just result equality. It preserves all registers and pc in the final state, final status and halted value, every positioned transition with its pre-state/instruction/after-state, ordered attempted reads and replies, instruction count and ordered categories. Each of the six category counts is a projection of this same ordered category list. It applies to every fuel prefix, including zero fuel, faults, early halts and running states stopped by missing code.

The induction reuses the same program and memory arrays, transfers the destination guard using the preserved register size, and invokes the operation theorem at the actual fetched instruction. `runFinite_size` separately proves the final register bank has exactly the initial size for every fuel.

The direct list-facing consumer is:

```lean
theorem runFinite_ofState (memory : Memory) (program : Program)
    (capacity fuel : Nat) (s : State)
    (hwrites : ∀ i ∈ program, i.WritesOnly (fun r => r < capacity))
    (hzero : ∀ r, capacity ≤ r → s.regs r = 0) :
    (runFinite memory.toArray program.toArray fuel
      (FiniteState.ofState capacity s)).decode = run memory program fuel s
```

This consumer composes `runFinite_decode`, exact array/list roundtrips and `FiniteState.decode_ofState`. It fixes the allocation and instruction identity on both sides. The lead can instantiate it with the accepted PQ1 program and allocation, query capacity and initial-state zero-tail theorem. This leaf has not yet compiled that canonical instantiation, so it does not alone close `REQ-NATIVE-FINITE` or the required capstone.

## Acceptance reach and limits

The frozen matrix remains unchanged. Evidence contributed here addresses the container/simulation portion of `REQ-NATIVE-FINITE` and the operational equality portion of `INV-TRACE-EXECUTION`, `INV-STORE-AGREEMENT`, `INV-READ-BACKING`, `INV-NO-SYNTHETIC` and `INV-CATEGORY-SEPARATION`. The exact same program/memory transformation in `runFinite_ofState` is the local identity link needed by `INV-STORE-IDENTITY` and `INV-PUBLIC-COMPOSITION`.

The leaf does not turn these whole-task rows CLOSED. In particular, word/limb width, arithmetic faults outside the safe domain, modeled address bounds, counted payload identity at the allocation theorem, canonical all-size instantiation, source compilation assumptions, binary parsing, native ownership, independent runtime controls and the final capstone remain downstream obligations. `runFinite` stores the entire proof observation trace; the lead's `Thin.lean` consumer erases it by a projection theorem and is the intended runtime path.

Anti-vacuity analysis: the positive predicate is whole decoded run equality for all arrays, fuel and finite states under the same destination guard. Replacing a successful loaded word, discarding a failed receipt, altering a category, or changing the final status would invalidate that exact theorem. The proof directly consumes the loaded cell and all transition fields. No mutation campaign was run by this leaf, and this analysis is not labeled a passed replay or closure of `INV-MUTATION-REPRODUCIBILITY`. The lead owns persistent exact-type consumers, source mutation controls and the final independent reference registry.

## Verification evidence

Platform: Microsoft Windows NT 10.0.26200.0; PowerShell 7.6.5; pinned compiler executable `C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe`. The executable was called directly, bypassing the elan shim's unwanted network fetch. All builds were one-job (`-j1`) and strictly sequential under the lead-granted sole build slot. No aggregate gate or shared mutable build cache was used.

Every compile used `Invoke-RMQOwnedBoundedProcess` from `scripts/owned_process_tree.ps1`, `WorkingDirectory` equal to the worktree, output limit 262144 bytes, `TempRoot=.lake/native-finite-logs`, and environment `LEAN_PATH=<worktree>/.lake/build/lib/lean`. Ownership was reported as `kill-on-close-job`, with `TimedOut=false`, `OutputLimitExceeded=false`, and empty `TerminatedIds` in every result. The helper removes its temporary output files; this table retains the actual command results. No timed-out or unexecuted host branch is represented as passed.

The repeated command shape, with each module substituted, was:

```text
lean.exe -j1 -o <worktree>/.lake/build/lib/lean/RMQ/Core/WordRAM/<module>.olean RMQ/Core/WordRAM/<module>.lean
```

| Owned stage | Module | Deadline seconds | Duration seconds | Exit | Outcome |
| --- | --- | ---: | ---: | ---: | --- |
| finite-prereq-Primitive | Packed/Primitive | 300 | 16.746 | 0 | Empty stdout/stderr |
| finite-prereq-Calculus | Packed/Calculus | 300 | 22.690 | 0 | Empty stdout/stderr |
| finite-prereq-Structured | Packed/Structured | 300 | 21.715 | 0 | Empty stdout/stderr |
| finite-prereq-Compiler | Packed/Compiler | 300 | 32.386 | 0 | Empty stdout/stderr |
| finite-prereq-Frame | Packed/Frame | 300 | 18.540 | 0 | Empty stdout/stderr |
| finite-prereq-Scratch | Packed/Scratch | 300 | 17.449 | 0 | Empty stdout/stderr |
| finite-leaf-01 | Native/Finite | 300 | 11.188 | 1 | Elaboration repair needed: constructor equality lemma name, declaration unfolding syntax, state equality rewriting and unavailable congrArg₂ |
| finite-leaf-02 | Native/Finite | 120 | 11.736 | 1 | Remaining zero-tail simplification and load-branch equality repair |
| finite-leaf-03 | Native/Finite | 120 | 11.405 | 1 | Remaining underspecified load simplifier produced metavariables; replaced with explicit constructor proofs |
| finite-leaf-04 | Native/Finite | 120 | 14.320 | 0 | All leaf declarations check; empty stdout/stderr |

The initial 300-second deadlines supplied cold-cache margin; later 120-second deadlines followed the observed 11-second Finite checks. Each retry followed a material proof edit, and the preceding owned process had already exited. No expensive unchanged timeout retry occurred. These commands produced `.olean` objects only; the lead was informed that generated C is still required for the route experiment.

Checked source size: 11537 bytes. SHA-256 of `RMQ/Core/WordRAM/Native/Finite.lean` after the final successful compile: `8edc747f2f0bbb7d4e6f6849b63869016969c4f7535d62e99a6e4d01901223df`.

`git diff --check` returned 0 on the working tree after leaf verification; Git also printed its line-ending notices for the lead-owned design ledgers. The focused prohibited-token/trust scan over Finite.lean had no matches (rg exit 1). Full repository hygiene, exact declared axiom inventory and typed consumer compilation are owned by the lead's phase report; the lead was specifically asked to include `executeFinite_decode`, `runFinite_decode` and `runFinite_ofState` in its explicit axiom inventory. No full build or aggregate gate was run here because the bounded leaf's direct module check is the proportionate development check and the host-wide final slot is coordinator scheduled.

## Proof digestion and decisions for the lead

Conceptually, the proof replaces all unbounded indexed stores used by this executor with concrete arrays, then relates actual array updates to the reference register function one instruction at a time. An arbitrary finite initial state decodes to an infinite zero-tail reference state. A reference initial state can be encoded exactly whenever its omitted registers are zero. Fuel induction preserves the exact bank size, allowing the write guard to remain stable.

In plain English, running this finite-bank executor produces exactly the same machine execution as the accepted primitive evaluator on the same code and memory, provided the bank is large enough for every register it writes. The theorem still sees incorrect memory contents and failed loads; they have not been excluded to obtain an easy success theorem.

Live assumptions: natural-number cells and operands, fixed finite register capacity, destination bounds for every fetched-program instruction, and a zero tail when importing an arbitrary reference state. There is no fixed-width or native-speed conclusion here. The downstream consumers are the lead's trace-erasing `runThin` projection, the canonical PQ1 instantiation, and finally `nativeExecutionCapstone_holds`.

A skeptical graduate student should next demand the actual canonical query's destination-bound and initialization facts, the checked limb/word refinement, and a proof that the shipped native entry point calls this exact core with checked marshaling. Those are mapped to the unchanged frozen requirements; they are not reclassified as optional hardening.

Design rationale for the lead's append-only ledger: keep `Scratch.Instruction.WritesOnly` as the guard instead of introducing a parallel register-liveness API; use zero-tail decoding so bounded writes suffice even when source identifiers are unbounded; use whole-Run equality rather than a result-only relation that loses failures, order or pre-state provenance; retain Nat cells as an explicit intermediate layer pending the separately assigned width work. The rejected alternatives are changing fetch alone, keeping closure registers, or treating finite Nat arrays as proof of finite-width machine storage. No ADD/process change was made by this leaf. Shared decision ledgers, family prose and digestion entries are owned by the lead and were not edited here.
