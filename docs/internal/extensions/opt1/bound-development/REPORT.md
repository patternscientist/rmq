Status: INCOMPLETE
Phase: branch-bound leaf kernel-checked; OPT-1 query instantiation and compact compilation remain lead-owned. This report claims no full acceptance row or roadmap closure.

Handle: OPT-1 / delegated bound_proof leaf.
Title: (OPT-1) Tighten and compact packed compilation.
Branch: codex/opt-1-packed-compiler.
Worktree: C:/Users/poin/.codex/worktrees/1580/RMQ.
Base, HEAD and governance: 0e6a00f654abc64f8b68988fa9675b9a839dca2f.
Commit: none by this leaf, as explicitly assigned. Root owns staging, shared ledgers and commits.

Owned proof: RMQ/Core/WordRAM/Optimization/BranchBound.lean.
Owned evidence: docs/internal/extensions/opt1/bound-development/PLAN.md, check.ps1, Axioms.lean, per-command JSON records, hygiene.json and this report.
Frozen overall matrix: docs/internal/extensions/opt1/ACCEPTANCE_MATRIX.md (read only by this leaf).

Personal startup verification passed scripts/project_skill_preflight.ps1 -GovernanceRef 0e6a00f654abc64f8b68988fa9675b9a839dca2f -RequiredSkills rmq-proof-sprint -RuntimeProjectSkills 'rmq-coordinator,rmq-proof-sprint,rmq-audit-prompt'. Expected/checkout/working/runtime catalogs each contained those three canonical skills. The leaf read the canonical proof skill, AGENTS.md, the complete completion gate, frozen matrix, baseline compiler/structured/calculus source, accepted E1/PQ1 roadmap entry and relevant compiler design entries. The lead had already created the branch and initialized frozen docs; this leaf did not reuse or reset another branch.

Checked declarations (all in RMQ.SuccinctFinal.PackedWordRAM.Optimization):

```lean
def branchBound : Structured.Block → Nat
  | .skip => 0
  | .action _ | .exit _ => 1
  | .seq first second => branchBound first + branchBound second
  | .ifZero _ zero nonzero => max (1 + branchBound zero) (2 + branchBound nonzero)
  | .repeat count body => count * branchBound body

theorem branchBound_le_size (block : Structured.Block) :
  branchBound block ≤ block.size

theorem compile_realizes_branchBound (memory : Memory) (program : Program)
    (block : Structured.Block) (base : Nat) (s : State) (hpc : s.pc = base)
    (host : Structured.HostedAt program base (block.compileAt base)) :
    Structured.Realizes memory program s (block.eval memory (Structured.Data.ofState s))
      (base + block.size) (branchBound block)

theorem compiled_run_bound_and_fuel_eq (memory : Memory) (block : Structured.Block)
    (s : State) (hpc : s.pc = 0) (a b : Nat)
    (ha : branchBound block ≤ a) (hb : branchBound block ≤ b) :
    (run memory (block.compileAt 0) a s).steps ≤ branchBound block ∧
    run memory (block.compileAt 0) a s = run memory (block.compileAt 0) b s
```

Expanded Realizes conclusion, explicitly pinned by BranchBoundConsumers.realizes_expectedType:

```lean
∃ final transitions,
  RunsTo memory program s final transitions ∧
  Structured.Data.ofState final = (block.eval memory (Structured.Data.ofState s)).final ∧
  transitions.filterMap (fun t => t.receipt) = (block.eval memory (Structured.Data.ofState s)).reads ∧
  transitions.length ≤ branchBound block ∧
  (final.status = .running → final.pc = base + block.size)
```

RunsTo is the existing predicate `run memory program transitions.length s = Run.mk final transitions`. Thus the transitions are produced by the actual baseline interpreter. The proof does not construct a semantic result and then decorate it with unrelated reads. Induction follows compileAt with its unchanged addresses: sequence composes actual segments, the zero arm incurs the conditional instruction plus its body, and the nonzero arm additionally incurs the forward jump if still running. Repetition uses the existing expanded compiler and multiplies the body bound. An early halt or failed load absorbs the rest of a sequence or repetition.

For standalone code, the realized final state either has stopped status or points exactly at the first position after the compiled list. In both cases `step = none`. The proof extends that SAME realized run to each supplied adequate fuel a and b. Its steps are then bounded by the realized transition length, not merely by a or b. Full Run equality preserves registers, final status, PC and every transition; consequently it preserves the result, ordered receipts including failures and repetitions, and categories. There is no initial-running, memory-shape, successful-load, endpoint, or eventual-halt hypothesis. The only standalone control-flow guard is initial PC zero, and the two numeric guards are that a and b exceed the structural bound.

Boundary evidence in BranchBoundConsumers:
- execution_expectedType independently pins both adequate fuel arguments, the step bound and full run equality.
- realizes_expectedType independently pins the expanded operational witness and all its object arguments.
- branch_directions: an emitted five-instruction branch-and-halt program has structural bound four, with zero-path result seven in three steps and nonzero-path result eight in four steps.
- one_short_truncates: three steps leave that nonzero execution running; four halt with eight. The adequacy guard is necessary on an actual execution.
- empty_branches_at_boundary: empty arms execute one or two steps and the latter finishes at PC two, the exact code boundary.
- repeated_loads: zero, one and three iterations retain zero, one and three literal receipts in order; the three-iteration program halts with seven in four steps.
- failed_load_stops: an empty memory faults after one load with exactly the attempted receipt (zero, none).
- nested_early_exit: nested sequencing and repeated trailing loads do not run after an earlier halt, preserving no reads and one actual step.
These are operational boundary consumers, not a claimed exhaustive registry or mutation campaign. Fresh compact counters, compact jumps, malformed metadata and query-specific controls remain assigned to the lead's compact/replay lane.

Command evidence and observed outcomes:
- The elan `lake --help` shim failed while attempting a network download. The exact pinned toolchain was already installed; direct `C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lake.exe --help` succeeded and printed Lean 4.22.0. No download or installation was performed.
- Pinned Lake rejects `-j1` as unknown. The leaf compiled the small import chain sequentially with exact installed `lean.exe -j1 -o <task-local artifact> <source>` and LEAN_PATH=<worktree>/.lake/build/lib/lean. No alternate toolchain, mutable shared cache or config change was used.
- check.ps1 uses scripts/owned_process_tree.ps1. Every subprocess had a 180-second deadline, 1 MiB output bound, Windows kill-on-close-job ownership, captured exit/stdout/stderr and per-run command/source-hash/platform records. No process timed out or exceeded the output limit; no host cleanup branch was claimed independently tested.
- Baseline cold prerequisites, all exit zero: Primitive 33.478 seconds; Calculus 20.690; Structured 13.983; Compiler 23.473.
- Initial BranchBound exit zero in 11.301 seconds. After adding the exact-type/boundary consumers, final BranchBound exit zero in 10.750 seconds; no warning or error output. The second check was required by the new declarations.
- Axioms.lean exit zero in 6.174 seconds, explicitly printing all three leaf theorem declarations and both typed consumers plus all six operational controls. The core execution bridge and typed consumers use only propext, Classical.choice and Quot.sound. branchBound_le_size uses propext and Quot.sound; the boundary controls use propext only. No new axiom or trust primitive is introduced.
- Full requested trust hygiene and native-decide scans over RMQ and lakefile.toml found zero matches (rg exit one means no matches). git diff --check exited zero. A separate no-index whitespace check included the as-yet-untracked BranchBound file and produced no whitespace diagnostics; its exit one records the expected new-file difference. Git emitted only its normal LF-to-CRLF advisory. The root must also run the required committed-range check after staging and commit.
- Full lake build, aggregate gates, query consumers, public prose checks and exact-commit blind audit were not run by this leaf: they belong to the root/coordinator final phase. No GATE PASS is claimed for them.

Final checked proof source SHA-256:
277A92EBF330770D992795D510DDBCEBF2CC51CAD49666E3C70E92E9083E8004

Proof digestion:
The conceptual change is to separate code positions from charged path length. The old static size still resolves every branch target and end PC, while a new independent recurrence bounds the transitions along one control-flow path. In plain English, the proof stops charging both arms of a conditional while continuing to charge the branch and the extra nonzero jump. It proves that giving the original program less but adequate fuel produces exactly the same execution, rather than merely proving that a truncated execution has few steps.

Live assumptions are the existing natural-valued primitive machine and compileAt definitions, code hosting and initial PC, plus adequate numeric fuel for the comparison theorem. There is no new physical-width/space claim in this pure generic compiler leaf. The named downstream consumer is root-owned Optimization/Capstone.lean branchSensitiveQueryBound, which must instantiate the original query source plus halt, rederive the concrete bound and identify the original queryRun and queryProgram. The compact capstone then remains required. A skeptical graduate student should ask whether that concrete instantiation uses the unchanged old adequate fuel and the exact same program/allocation; this generic theorem supplies full equality once the root proves those identities, but does not silently claim the instantiation itself.

Design notes for root's append-only ledgers:
The additive Optimization module re-proves the baseline compiler's private proof helpers because shared Packed files are read-only for this extension. Replacing the old theorem/budget identity or changing target-address arithmetic was rejected. The generic theorem keeps old sizes for addresses, uses branchBound only for transitions/fuel, and keeps the baseline primitive transition type. The direct installed Lean -j1 invocation is the process workaround for the pinned Lake CLI and shim behavior; it preserves exact toolchain and one-process build ownership. Root owns the relevant task-scoped DESIGN_DECISIONS and WORKFLOW_DESIGN_DECISIONS entries, which this leaf intentionally did not edit.

Build ownership was explicitly released to the lead after the axiom check. No Lean/Lake command remains running. The leaf can be consumed immediately; OPT-1 remains INCOMPLETE until its full frozen matrix, compact implementation, required verification and coordinator audit close.
