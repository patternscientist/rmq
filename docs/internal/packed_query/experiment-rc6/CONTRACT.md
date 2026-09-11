# Whole different-block instruction experiment

Baseline: audit-v1-rc-6, 4639223bc8130b0ef752270b5cbdd74325abcd60.
This isolated experiment does not alter the candidate or adopt a public model.
Consumer: decide whether a universal instruction theorem is a preferred v1 endpoint.

Frozen requirements (before implementation):

| ID | Requirement | Evidence and anti-vacuity test |
|---|---|---|
| Q1 | Execute a complete different-block query, including crossing-cell decoding, both selects, fringes, interior reads and final rank, using charged instructions on the same allocation. | Primitive VM executes a program with endpoints in registers; compare ordered physical and logical receipts against RC6 and result against independent leftmost List Int specification; require all stages actually reached. |
| Q2 | Success would justify making the universal instruction theorem a preferred v1 endpoint. | Assess finite success and remaining uniform proof obligations separately; do not claim a universal theorem from fixtures. |
| I1 | Same allocation, read backing, actual execution trace, and value dependence. | Export canonical memory directly from Lean; VM receives only numeric cells and endpoints; remove/corrupt cells and check result/control failure. No query-derived code, replay, or host RMQ callback. |
| I2 | Every computation is a charged primitive. | Restricted source compiled to fixed register instructions. No semantic controller/rank/select primitive. Geometry, decoding, routing and loops are compiled too. Six category counts partition executed steps. |
| I3 | Width and address discipline. | Check all reachable values and every instruction operand/target (including dormant code) against declared width; crossing decode keeps two cells separate. Check failed reads too. |
| I4 | Public-size parameters only in program generation. | Compiler constants derive only from n; LONG and SPARSE recovered by charged reads. Compare same-n program across shapes/queries. Record size-specialization/uniform initialization limitation. |
| I5 | Half-open, leftmost semantics, including invalid control. | Independent reference minima including ties; empty/reversed/out-of-range intervals reject with zero reads. |
| V1 | Reproducible checks. | Versioned exporter, compiler, programs and runner; logs/results. Direct Lean check exporter; warm lake build; source hygiene and diff check. |

Verification coverage: development-loop compiler and fixtures; final-required complete matrix and negative controls, exact code/memory hash, independent reference, receipt equality and width/category checks. No new public proof is claimed. Full RC6 aggregate gate was already completed for unchanged source and is not repeated for an external experiment.

Experimental ISA: ordinary unsigned registers, natural saturating subtraction (implemented as explicit compare/branch/sub when necessary), arithmetic/comparison/bit operations, loads, conditional branches, and halt. Variable shifts and variable division are explicit additions beyond E1's constant-multiplier/divisor ISA, to be assessed, not silently adopted. No popcount, bit-vector scan, or RMQ operation is primitive. Missing physical reads halt with a failure result and remain counted. Finite width failures must be reported or repaired, not hidden with Python arbitrary precision.

Final evidence (requirements above remain unchanged):

| ID | Disposition |
|---|---|
| Q1 | Passed the full path on seven reference fixtures, with exact logical and physical receipt equality; two further cases cover no-interior and invalid paths. Primary: 57,223 steps,107 reads,17-bit original allocation. |
| Q2 | Preferred next v1 endpoint, conditional on the model/metadata/width work detailed in ASSESSMENT.md. Universal theorem remains open. |
| I1 | Canonical export, reference-isolated build/run interfaces, positional comparisons,26 cell mutations and missing-header failure. Finite evidence only. |
| I2 | Primitive VM and independently written Lean evaluator agree on all nine saved cases. Calls/returns and Nat-subtraction lowering charged; four compiler edge checks pass. Acyclic subroutines replaced excessive inlining after the initial static-width check rejected it. |
| I3 | All saved cases and 1,705 query executions pass dynamic and constructor-exhaustive static width checks. Full-width logical tags and very-small-size program addressing remain universal-proof obligations. |
| I4 | Same-n code hashes identical across shapes/queries; LONG/SPARSE read at runtime. All executed canonical counts zero; uniform metadata setup remains open. |
| I5 | 721 valid and984 invalid query checks pass, including ties and zero-read rejection. 1,584 distinct input/endpoint cases. |
| V1 | reproduce.ps1 exits successfully; candidate warm lake build, source hygiene and diff check pass. New Lean files directly elaborated/run. No new public theorem or aggregate-gate claim. |
