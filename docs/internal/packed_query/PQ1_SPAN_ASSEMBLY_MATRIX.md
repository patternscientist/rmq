# PQ1-SA frozen acceptance matrix

Base: 9e2720b991e203d22a2787abf66dbfb9888088fb. Governance: 4639223bc8130b0ef752270b5cbdd74325abcd60. Branch: codex/fully-charged-packed-query-v1. Scope: fixed scalar source and compiled numeric span routine. No staging/commits.

## Verbatim frozen requirements

- REQ-SA-SOURCE: Define spanBlock base independent of width, position, len and memory. Input registers are base,base+1,base+2; output is base+3; scratch uses an explicitly bounded interval starting at base+4. For running source Data with those inputs, prove if decodeSpanNat width position len memory=some value then evaluation ends running with output value, and if it is none evaluation ends fault. Cover every positive width and len<=width mathematically; no successful-read premise. Use only Action scalar operations and Block branches/sequence. Make len<width the live canonical machine-safety domain if a power-of-two mask needs it, while keeping the value theorem honest about the mathematical source domain.

- REQ-SA-RECEIPTS: Define exact attempted receipts from the same numeric memory: none for zero span, first attempt for a nonzero span, second only if crossing and first succeeds. Prove source eval reads equals this ordered list for all cases, including missing first or second cells. Do not identify the full planned list with a short-circuited failed execution.

- REQ-SA-FRAME: Prove registers outside the declared input/output/scratch interval are unchanged, and source size/maximum static register ID are bounded by explicit constants independent of inputs and memory. Constant immediates and encoded program fields must be inventoried; static expansion may not depend on runtime width.

- REQ-SA-MACHINE: Once Compiler.lean is available, provide an actual primitive-run consumer of spanBlock that proves the same result/status and ordered receipts with a fixed instruction budget derived from spanBlock.size. Frame and all actual steps must refer to that same run. Coordinate required compiler theorem interfaces with primitive_calculus; do not stop at the source evaluator if this dependency is locally available.

- CHK-SA-LEAN: Narrow checks plus direct compiled consumers for zero, crossing, noncrossing, missing-first, missing-second and all-ones raw cells. No native_decide or desired-answer hypotheses in the canonical source implementation.

- `INV-VALUE-DEPENDENCY`: returned values and routing decisions depend on
  actual charged reads, not a semantic answer computed before the reads. When
  the requirement concerns the returned answer or route, evidence must constrain
  that value, state, or route; inequality of an enclosing trace record can be
  satisfied by its log alone and is insufficient;

- `INV-TRACE-EXECUTION`: traces and footprints are derived from the execution
  they describe;

- `INV-READ-BACKING`: every successful read is backed positionally by the
  counted store;

- `INV-INSTRUCTION-ATOMICITY`: each modeled small step performs the familiar
  primitive operation it advertises. A constructor whose evaluator body hides
  recursion, a variable-length scan, repeated rank/select work, decoding, or
  several arithmetic categories is a macro-step unless that work is expanded
  into charged transitions or bounded by an explicitly accepted primitive;

- `INV-NO-SYNTHETIC`: synthetic events, decorative rereads, and post-hoc replay
  do not support the execution claim;

- `INV-PROOF-SEPARATION`: proof-only fields never carry answers or uncharged
  routing information;

- `INV-CATEGORY-SEPARATION`: payload bits, proof fields, model ticks, machine
  state, Lean runtime, and measured performance remain distinct.

## Fixed source/register contract

spanBlock base receives width, position, len in base, base+1, base+2. Output is base+3. Scratch is the ten registers base+4 through base+13; no other register is modified. Static source size is 22 primitive instruction positions before an optional final halt. Source uses only scalar Action instructions and Block sequence/ifZero; constants are 0 and 1. The source value theorem covers 0<width and len<=width (and may prove a stronger mathematical statement). The canonical runtime-safety consumer must use len<wordWidth for power masks; static syntax bounds alone are not runtime safety.

## Evidence matrix

| ID | Exact evidence/consumer obligation | Anti-vacuity challenge | Status |
| --- | --- | --- | --- |
| REQ-SA-SOURCE | Actual spanBlock.eval on running numeric inputs has running output exactly decodeSpanNat some value, or fault exactly on none. | Crossing, zero, absent first/second, all-ones cell. | CLOSED. `spanBlock_source` proves `SpanOutcome base (decodeSpanNat width position len memory) actual.final` and exact reads for every numeric width/position/len, assuming only the three input-register equalities. `SpanOutcome` expands to running plus exact output for some, or fault for none; direct some/none projection theorems consume it. The mathematical domain is stronger than the assigned positive-width len≤width domain; canonical machine safety remains len<wordWidth. |
| REQ-SA-RECEIPTS | Same evaluation reads = exact memory-based attempted receipts, stopping after failed first. | Distinguish planned two cells from single failed attempt. | CLOSED. `spanBlock_source` and `spanRun_correct` equate source and actual machine reads respectively to `spanAttemptReceipts width position len memory`. Its definition has zero attempts for zero length, one for missing first, and a second only after first success in a crossing. Six compiled examples check the exact lists; `spanAttemptReceipts_length_le` proves ≤2. |
| REQ-SA-FRAME | Every register outside [base,base+14) unchanged; size=22; static field bounds and literal inventory. | Arbitrary external register, dormant branches, varying runtime width. | CLOSED. `spanBlock_frame` preserves every r<base+3 or base+14≤r, including inputs, even on faults. `spanRun_prefix_frame` preserves every outside-[base,base+14) register for every actual primitive fuel prefix. `spanBlock_size=22`, `spanRoutine_size=23`, `spanProgram_length=23`; static-field theorems bound every register by base≤r<base+14 and every encoded tag/operand by base+pc+22 (body) or base+23 (wrapper). `spanBlock_compilation` lists every instruction and target, with only scalar constants 0 and 1. |
| REQ-SA-MACHINE | Compiler consumer proves actual primitive-run result/status, same reads, same register frame and fixed budget. | Source-only proof insufficient; compare actual run projections. | CLOSED. `spanBlock_machine` consumes `Block.compile_correct` to give an actual hosted segment with derived used≤22, exact output/status/reads/frame, steps=used and continuation PC. `spanRun_correct` consumes `Block.compile_run` for the same 23-position halt wrapper: actual result=decodeSpanNat, actual terminal status=fault or halted decoded value, exact ordered attempted receipts, final frame and steps≤23. `spanRun_inputs` discharges input equalities; `spanRun_steps_partition` proves exact six-category partition for that same run. |
| CHK-SA-LEAN | Narrow source and compiled universal checks plus six direct compiled boundary consumers. | Literal expected results from bit slices. | CLOSED. Final standalone Lean emitted .olean/.ilean with exit0, no warnings, 5.71s. Compiled zero/contained/crossing/missing-first/missing-second/all-ones cases check result or fault, exact receipts and exact step counts 3/14/19/5/11/14. Returned-value dependency has separate checked inequalities. Hygiene, frozen byte verification and new-file whitespace results are recorded in the report. |
| INV-VALUE-DEPENDENCY | Source and actual run output projection = same numeric decoder; reads supply both fragments. | Mutating a consumed bit changes result, not only receipts. | CLOSED. Universal source and primitive equalities constrain returned values directly. `SpanCompiledExamples.returnedValue_dependency` checks first and second reply changes against the actual primitive result, not a trace record. No universal sensitivity to irrelevant bits is inferred. |
| INV-TRACE-EXECUTION | Attempted receipts agree with source eval and actual primitive run. | First missing load has exactly one receipt. | CLOSED. `spanBlock_machine` and `spanRun_correct` use Compiler adequacy to identify receipts of the exact primitive run with the same source evaluation and scalar memory-based attempted list. Compiled missing-first has [receipt0-none] with5 actual steps; missing-second has [receipt0-some13,receipt1-none] with11. |
| INV-READ-BACKING | Exact attempted receipts use memory at actual positional addresses; machine provenance from run. | Failed and second successful occurrences. | CLOSED. `spanAttemptReceipts_backing` retains occurrence/index and proves reply=memory[address]?. `spanRun_read_at` retains the actual transition index, prefix pre-state, fetched instruction, execution equation, address-register value and same-memory reply, for both successful and failed loads. |
| INV-INSTRUCTION-ATOMICITY | All source leaves compile to familiar scalar Action instructions; every step charged. | No decoder macro leaf or hidden runtime loop. | CLOSED. Literal compilation has22 scalar actions/branch/jump positions, plus one halt in the wrapper. Each action is one existing Primitive instruction; runtime shifts/division/remainder are scalar operations, and no repeat or decoder action exists in spanBlock. The actual run budget comes from Compiler adequacy, with exact category partition and fixture step counts. |
| INV-NO-SYNTHETIC | Receipt list derived from same evaluation/run, no replayed second failure attempt. | Missing first short-circuits. | CLOSED. Decoder arithmetic follows actual raw loads. Compiler proves evaluation-to-run receipt equality, and the attempt-list definition short-circuits on first absence. Exact compiled failure receipts refute a phantom second attempt. |
| INV-PROOF-SEPARATION | Fixed executable source takes base only; numeric inputs reside in registers and memory. | No semantic answer/proof field. | CLOSED. `spanBlock` takes only register base, while width/position/len and memory enter primitive execution through registers and memory. `spanInputRegisters` sets only scalar inputs. Neither source construction nor program compilation receives a decoded answer or proof field. |
| INV-CATEGORY-SEPARATION | Source evaluation distinct from primitive budget/width and native runtime. | Size and static fields alone do not prove runtime safety. | CLOSED. Source theorem is mathematical Nat evaluation; machine consumer proves actual familiar-instruction execution and budget. Encoded-field bounds are expressly static. Canonical per-state Instruction.Safe/width proof and whole-query capstone remain lead-owned as explicitly scoped; no native runtime bound is asserted. |

## Verification plan

Use the single coordinated build slot for standalone narrow Lean checks against .lake/build/lib/lean. Expected warm runtime is seconds; diagnose surviving processes if a timeout occurs. Final leaf checks: source and compiled consumers, owned-file hygiene, strict UTF-8 frozen-block equality, no-index whitespace for new files. Lead owns exact-base strict design, committed-range whitespace and whole-query/final public gates. No mutation campaign assigned or claimed.

## Template policy

# Proof Acceptance Matrix Template

Freeze this matrix before implementation. Prompt requirements and coordinator-
assigned inherited IDs do not change after work starts unless the coordinator
records an explicit contract amendment. Evidence and status may evolve.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `REQ-01` | Copy prompt text verbatim. | Local or roadmap | State the conclusion that would entail it. | Name every link to the consumer. | Attempt a concrete way this could be false and name what rejects it. | Quote the checked theorem type/result; a name alone is insufficient. | Open |
| `INV-...` | Copy the assigned invariant from `COMPLETION_GATE.md`. | Inherited | State the required conclusion for this target. | Identify the exact object(s). | Include semantic mutations and tiny/threshold/dead/invalid cases as applicable. | Fill after proof/check. | Open |
| `CHK-01` | Copy the requested command. | Verification | Exit success plus relevant output. | Name the surface covered. | State important uncovered scope. | Fill after running. | Open |

Rules:

1. A row is closed only when the evidence conclusion entails the exact
   requirement for the named consumer.
2. If two claims concern different payloads, stores, executions, widths, or
   queries, show a proved identity/equivalence chain or leave the row open.
3. For Lean evidence, quote the theorem type or list every hypothesis and
   conclusion. Do not substitute a declaration-name inventory.
4. Record counterexamples and semantic mutations actually attempted for every
   applicable semantic subclaim, their outcomes, and the theorem or definition
   that rejects them. Merely naming one easy falsifier for a bundled row is not
   enough. A passing build is not semantic evidence for a requirement.
5. Keep local-rung and roadmap-node rows distinct.
6. The worker may report `CANDIDATE_COMPLETE`; only the coordinator records
   `ACCEPTED`, and designated public capstones also require fresh blind audit.
7. For liveness, coverage, ownership, dependency, and composition rows, expand
   load-bearing definitions. A predicate made true by definition, a manually
   restated enumeration, aggregate-record inequality caused only by its log, or
   guarded/unguarded object mismatch leaves the row open.
8. Projection-specific evidence must match the quantification and validity
   domain of the requirement. A singleton executable witness does not close a
   universal dependency row.
9. Every semantic mutation row must record the accepted predicate `P`, the
   rejected predicate `Q`, and all guards and quantifiers. Require `P = Q` or a
   checked implication `P -> Q`; otherwise leave the row open.
10. Distinguish component may-read, component successful-read, top-level
    reachable-read, and actual emitted-occurrence claims. Evidence at one level
    does not silently entail another.
11. For provenance rows, state whether evidence preserves only event values or
    also occurrence position, multiplicity, producing instruction, folded
    pre-state, and invocation parameters. `List.Mem` alone is event-value
    evidence.
12. A worker cannot narrow a row by calling residual work "strictly stronger"
    or future hardening. Record an explicit coordinator-approved contract
    amendment or keep the row open.
13. For classifier/linter rows, finite fixtures are lower bounds. Freeze the
    category boundary, add category-level holdouts and allowance-bypass
    mutations, and test the production final verdict across supported path and
    parser shapes. A copied regex or whole-file bypass cannot close the row.
14. For small-step machines, inspect evaluator bodies. A constructor/category
    inventory plus one step per constructor does not close atomicity when one
    branch hides recursion, variable-length work, or several primitive
    categories.
15. Expected executable results must come from an independent specification;
    an implementation result cannot serve as its own test oracle.
16. Width evidence must enumerate every encoded constructor field, including
    dormant instructions, register identifiers, and control-flow operands.
17. Account for input-dependent constants stored in program code, and verify
    that executable validators import and mutate the new layer rather than only
    its predecessor.
18. After the final commit, run `git diff --check <exact-base>..HEAD`; a clean
    working tree alone does not certify committed whitespace.
19. For mandatory public-certificate fields, name a checked typed consumer that
    projects every exact field proposition and object argument. Record
    field-deletion, proposition-weakening, and sibling-substitution mutations;
    opaque record passage and constructor initialization do not establish
    anti-bypass consumption.
20. If closure cites a mutation campaign, identify the committed runner or
    stable fixtures, exact cases, expected verdict/failure surface, expected-
    accept controls, and restoration/clean-tree check. Report-only experiments
    and unreferenced Git objects leave `INV-MUTATION-REPRODUCIBILITY` open.
    For a public dependency, pin an expected type independently of the current
    theorem declaration and mutate the public proposition itself.
21. If the worker stops on an obstruction, put the exact frozen target and the
    obstruction proposition side by side, including domains, objects, guards,
    and quantifiers. Require a checked target negation or target-to-`False`
    implication. Separate arbitrary-state, shape-growth, and singleton-
    reachability witnesses need a checked bridge into one canonical reachable
    family; prose composition leaves the target row open. State whether the
    result obstructs only the current implementation/decomposition or every
    construction allowed by the contract.
