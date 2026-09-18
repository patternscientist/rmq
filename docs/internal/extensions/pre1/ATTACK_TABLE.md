# PRE-1 author audit of the complete historical catalogue

Catalogue: docs/internal/wf3_attack.json at
`0e6a00f654abc64f8b68988fa9675b9a839dca2f`. Exact distinct registry:
FK-1, FK-2, FK-3, FK-4, FK-5, FK-6, FK-7, FK-8, FK-9, FK-11, FK-12,
FK-13, FK-14, FK-15, FK-16. There are 25 comparison rows, not 25 distinct fakes;
FK-10 is absent. Contract B has 12 rows and five surviving attacks in the
historical comparison. This current audit assigns all 15 a disposition.

The verdicts below assess the **requirements of the amended contract**. The
builder is not yet implemented. A prospective exactness/workspace/execution
obligation is not recorded as an already-proved theorem. C1-C4 formal controls
and their exact types are separately indexed in the phase evidence table.

| ID | Historical B verdict | Current contract verdict and named rejecting obligation | Actual author evidence / remaining implementation requirement |
| --- | --- | --- | --- |
| FK-1 fabricated result and dummy log | Rejected | Forbidden by O-REPLAY together with operational run identity / INV-TRACE-EXECUTION | Plain-data Replays has fabricated_replay_rejected. Actual builder run/emission identity remains REQ-PRE-EXACT. |
| FK-2 oracle in interpreter | Rejected | Forbidden by O-FIREWALL + O-WORKCAP | Exact primitive imports and frozen evaluator bytes; actual canonical-BP oracle_not_reflected uses numeric result projection. A copied semantic implementation also requires changing the frozen evaluator. |
| FK-3 unbounded work in one instruction | Survives | Forbidden by O-WORKCAP / INV-INSTRUCTION-ATOMICITY | Exhaustive Prim scalar arms; actual bstep_reflects, literal cap 1, bounded encoded constants. Future loops must use these transitions and prove actual work, not add a macro. |
| FK-4 payload in input / preseeded cells | Rejected | Forbidden by O-POINTWISE, O-NOINHERIT and CleanTail | Exact header/key cell equations, signed representability/order facts, replacement locality, initial clean tails and reserve-fresh. Full physical input/key embedding and peak ownership remain required. |
| FK-5 payload in size/shape program | Survives | Forbidden by amended O-UNIF and INV-PROGRAM-ACCOUNTING | Same Uniform predicate for accepted program schema and baked_not_uniform. Actual program must have literal instruction/encoding pins and counted code. Finite fixed tables are counted; an all-size strict bit gap is not falsely claimed. |
| FK-6 decorative bridge to semantic result | Rejected | Forbidden by REQ-PRE-EXACT + INV-VALUE-DEPENDENCY | The required LHS is the emitted ordered output of the charged run; RHS is exactly PQ1 buildMemory. No builder theorem exists yet. Oracle rejection shows why RHS correctness alone is insufficient. |
| FK-7 replay advertised as anti-oracle | Survives as weakening | Disallowed claim by O-REPLAY; no claim that replay alone kills it | Contract explicitly separates replay from uniformity, primitive reflection, firewall, pointwise input and no-inheritance. The amended combination supplies separate obligations. |
| FK-8 real addresses / oracular write values | Rejected | Forbidden by O-WRITE / INV-VALUE-DEPENDENCY | store_value_from_prestate pins address and value to the same actual primitive prestate. Full positional occurrence/provenance proof remains required for the builder's emitted writes. |
| FK-9 adjustable padding or confused units | Survives | Forbidden by O-BITS / REQ-PRE-EXACT | Ordered equality to exact numeric buildMemory, both padding layers and 174 metadata words; no fittable padding parameter. Numeric stores cost word writes; input/output bit capacities multiply by fixed width. Future exactness still open. |
| FK-11 partial component called full | Not tested against B | Forbidden by O-COUNT / REQ-PRE-EXACT / INV-PUBLIC-COMPOSITION | Source inventory distinguishes outer components from interior five wrappers/eight tables. Full allocation equality is mandatory; no single-component fallback is a valid completion. |
| FK-12 width covers address only | Not tested against B | Forbidden by INV-WORD-WIDTH + INV-ADDRESS-WIDTH | Bounded constructor constants and pointwise input words are checked. Future execution safety must bound each written value, address, dynamic operand, sentinel and every reachable pre/poststate at the same width. |
| FK-13 nonexistent query theorem | Not tested against B | Forbidden by REQ-PRE-JOIN | Exact current producer is PackedWordRAM.fullyChargedPackedQueryCapstone_holds, Capstone.lean:173; the new capstone must consume it after efficientBuild_eq_buildMemory. Current source type inspected; actual new composition remains open. |
| FK-14 unbounded scratch | Survives | Forbidden by strengthened O-SCRATCH / REQ-PRE-COST | Initial clean-tail and single-cell allocation prevent silent preseeded extension. Full explicit peak temporary-word constants, ownership and retained-input/code/output accounts remain mandatory. |
| FK-15 unconstrained giant fuel | Rejected only as soundness attack | Rejected as an efficiency witness by REQ-PRE-COST | Actual executed work must be <= C*n+D with literal constants and interpreter reflection. Large enough fuel is only a termination instrument, never the cost theorem. No future bound is supplied in this phase. |
| FK-16 empty stores agree vacuously | Rejected | Forbidden by REQ-PRE-EXACT + INV-STORE-IDENTITY | Exact canonical ordered output includes 174 metadata words even at empty input; no empty-store sibling target. The source metadata length theorem fixes nonempty allocation; actual builder equality still open. |

The author check is 15/15 explicit dispositions, including the three missing
historical B verdicts. This is not 15/15 completed builder proofs. The
coordinator must independently reconstruct these obligations and commission
the mandatory blind exact-commit audit after the scheduled contract gate.

## Version 2 corrections (2026-09-12, auditor recommendation R4)

The fresh blind contract audit PRE-1-A1 (`docs/internal/audit_reports/2026-09-12_PRE1_contract_fresh_blind.md`, section 7 and recommendation R4) found that rows FK-1 and FK-5 above name the wrong rejecting basis or omit a reclassification. The corrected rows follow, in the same column shape as the version-1 table.

| ID | Historical B verdict | Current contract verdict and named rejecting obligation | Actual author evidence / remaining implementation requirement |
| --- | --- | --- | --- |
| FK-1 fabricated result and dummy log | Rejected | Forbidden by run identity: REQ-PRE-EXACT (exact ordered output equality; its frozen evidence row requires the "emitted-order proof from that same run") and REQ-PRE-MACHINE ("against that interpreter"), together with INV-TRACE-EXECUTION and INV-NO-SYNTHETIC. NOT by O-REPLAY, whose own text disclaims any kill ("Replay is necessary and insufficient"). | Plain-data Replays has fabricated_replay_rejected, which shows only that the toy Replays predicate is falsifiable. The load-bearing rejection is that efficientBuild xs is the positional projection of the accepted run's final memory (CONTRACT.md V2-3) and that work, safety and provenance are stated on that same run's transitions through checkedStep; a hand-built record with no run has no run to project. Remains a builder obligation. |
| FK-5 payload in size/shape program | Survives | Size/shape-indexed family: forbidden by amended O-UNIF (the actual Uniform predicate) and INV-PROGRAM-ACCOUNTING. Width-indexed re-entry: forbidden by AMEND-2's parameterless, literal-pinned constants (CONTRACT.md V2-2). Cheap variant (fixed shape-independent tables inside the one fixed program): NOT forbidden; counted code at the declared width via programWords/CodeAccounting. | Same Uniform predicate for the accepted program schema and baked_not_uniform. Both constants compile from one template with rfl literal pins and consumer-pinned numerals; builder replay cases (i) width/size parametrization and (ii) each literal numeral changed must fail at pinned consumer lines. Finite fixed tables are counted, and no all-size strict bit gap is claimed. |

The version-1 rows above are retained as history; for FK-1 and FK-5 these two rows govern.
