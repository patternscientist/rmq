# Complete packed-query instruction experiment

The experiment succeeds. I would now make a universal theorem for a fully charged packed query a **preferred v1 endpoint**, with an explicit instruction model and a small metadata change ahead of the proof. The result makes the whole-query integration risk substantially smaller. It does not yet establish a universal constant instruction bound or justify treating that theorem as already routine.

The audited construction is unchanged: `audit-v1-rc-6`, commit `4639223bc8130b0ef752270b5cbdd74325abcd60`. All additions are in this isolated experiment directory. Tests ran on Windows with Lean 4.22.0. Neither runtime timings nor the existing charged-trace 210 are used as instruction counts.

## What actually ran

For the primary input `[3,2,3,1,3,2,3,0,3]` and query `[0,9)`, the program returns **index 7**, the independent specification's leftmost minimum. It operates on the exact canonical allocation: **75 cells × 17 bits = 1,275 bits**. The complete execution takes **57,223 primitive steps**, makes **107 physical reads**, and contains **13 logical reads that cross a physical cell boundary**. Every executed register value, address and shift intermediate fits 17 bits. The largest register value is 84,001; the capacity is 131,072. Static checking also covers all instruction operands and targets, including dormant code.

The two selected closes are 4 and 17, in blocks 0 and 2. The program executes both selects, left rank seed/window/fringe, the local interior directory, right rank seed/window/fringe, and final rank. The middle leg makes **18 segment-20 logical reads**, including the sparse-level lookup, local selectors and all four summary fields. The whole query makes 93 logical reads, in addition to the three metadata-prelude reads. Empty logical words and absent logical words retain their different tags and issue no decorative physical loads.

The six counts partition the execution exactly:

| Category | Steps |
|---|---:|
| Physical memory reads | 107 |
| Register writes | 34,277 |
| Arithmetic and bit operations | 11,673 |
| Comparisons | 4,209 |
| Branches, including subroutine transfers | 6,956 |
| Halt | 1 |
| **Total** | **57,223** |

The ordered physical addresses and replies match RC6 position by position, including repetitions. The logical segments, indices, decoded replies, and each logical read's physical subtrace also match. This is stronger than checking only the final answer or total probe count.

The prototype is deliberately unoptimized. Its 4,444 instructions use 2,939 statically assigned register slots. Repeated geometry calculation and conservative operand copies dominate its count. These numbers are observations of this program, not a proposed public constant or a performance benchmark.

## How the execution avoids shortcuts

`ExportFixture.lean` obtains memory directly from `packedReviewerMemory` and reference traces from the actual RC6 controller and logical lowering. It converts each complete cell's bits to a little-endian integer. Its geometry export has type `Nat -> Json`: it cannot consult the input shape, endpoint pair, answer or runtime trace. Affine source geometry was also checked against the original definitions at the actual counts and sixteen formal count pairs.

`run_experiment.build` receives only n, the public width and n-only geometry. `machine.run` receives the resulting program, numeric physical cells, width and endpoints. Reference answers, input values and reference traces are passed only to the checker after execution. No logical store, controller callback, precomputed RMQ answer or trace replay enters the VM.

The restricted source is **compiled**, never called as a Python query. All address arithmetic, dispatch, decoding, rank/select folds, fringe folds, interior reads and comparisons become register instructions. Acyclic subroutines use parameter moves, a return-PC constant, a jump, and an indirect return jump; all are charged. There is no hidden call stack. Nat subtraction becomes an explicit comparison/branch/ordinary-subtraction sequence. Crossing decoding keeps the two physical cells in separate registers and combines only the requested pieces. The four-word fringe window also remains in separate registers.

`CheckMachine.lean` independently implements the primitive evaluator in Lean and consumes the emitted instruction array. On all nine exported reference cases, it agrees with the Python VM on the answer, every physical receipt, all six counts, total steps and maximum register value. This is an executable cross-check, **not** a kernel-checked all-input simulation theorem or a compiler-correctness theorem. Both evaluators consume the same compiled program, so this does not independently validate every aspect of source compilation.

## Measurements and adversarial checks

All listed valid reference queries are `[0,n)`:

| Fixture | n | Cell width | Answer index | Reads | Instructions | Nonempty interior covered |
|---|---:|---:|---:|---:|---:|---|
| Balanced pattern | 9 | 17 | 7 | 107 | 57,223 | Yes |
| Ascending | 9 | 17 | 0 | 104 | 54,412 | Yes |
| Descending | 9 | 17 | 8 | 90 | 42,590 | No |
| All tied | 9 | 17 | 0 | 104 | 54,412 | Yes |
| Mixed-sign zigzag | 15 | 18 | 13 | 131 | 70,373 | Yes |
| Comb shape | 15 | 18 | 0 | 122 | 64,775 | Yes |
| Balanced pattern | 16 | 18 | 7 | 136 | 59,611 | Yes |
| Mixed-sign zigzag | 29 | 19 | 27 | 140 | 71,600 | Yes |
| Invalid `[4,4)` | 9 | 17 | Rejected | 0 | 19 | No |

The broader campaign made **1,705 query executions**, comprising 721 valid and 984 invalid checks. There are **1,584 distinct input/endpoint cases**; the invalid-reference fixture repeats the 121-case balanced-input sweep. For n ≤ 16, the campaign exhausts endpoints from 0 through n+1. At n=29 it checks a deterministic endpoint grid plus singletons, prefixes, suffixes and invalid cases. Every result agrees with an independent leftmost minimum scan. Every invalid interval makes zero physical reads. Maximum observed values remain inside their declared widths. The largest observed count across these sweeps is 77,532 steps; this is not a universal bound.

For equal n, changing shape or endpoints produces byte-identical instruction code. Input values never enter program generation. The ascending and tied cases check leftmost tie behavior against different value-level inputs even though their Cartesian shapes agree.

On the primary fixture, flipping the least-significant bit in each of 26 distinct read cells gives four changed answer projections (successful answers become rejection), two failed runs, and twenty unchanged answers. These are dependency checks, not assertions that every stored bit affects every query. A missing header produces one counted attempted load and failure. Mutations can produce invalid data, so they do not establish correctness on corrupted memory.

An independent review caught a generic compiler evaluation-order defect involving global operands followed by effectful calls. Operands now snapshot through charged moves; four compiler edge checks cover that case, argument order, repeated acyclic calls and loop/subtraction behavior. The review also prompted explicit full-width mask handling and preservation of final-rank saturating subtraction. All reported counts are from the repaired program.

## What the result suggests for v1

**1. Prefer the universal instruction theorem, and start by fixing metadata recovery.** The current prelude computes `SPARSE` by scanning `SPARSESLOTS % SPARSEW` bits. Those steps are charged here; there is no hidden popcount. But the visible bound is proportional to word width, and the experiment supplies no uniform constant bound. This literal compilation therefore cannot currently support the desired constant-time conclusion. Existing E1 rank-table machinery does not immediately solve it: the fringe table's address already depends on the sparse count being recovered.

The most straightforward next design is to store the sparse count directly in an additional header cell. One extra O(log n)-bit cell should preserve the `2n+o(n)` form after the space and layout proofs are updated. That is a proposed follow-up construction, not a modification performed in this experiment, and it would require renewed layout, trace and cap proofs. Keeping the existing allocation instead requires a suitable bounded popcount implementation and its width proof. I would compare these two options briefly and favor the extra header cell unless preserving the one-cell header has independent value.

**2. Freeze a conventional explicit ISA and prove the whole-program refinement.** This experimental ISA extends E1 with register-register multiplication/division/remainder, variable shifts, bitwise operations and indirect jumps. Their costs are assumptions of this experiment. No rank, select, popcount or controller transition is a primitive. Decide which operations the paper's word-RAM permits before porting the proof. Then connect the primitive packed-read block to rank/select, fringes, interior and final rank, preserving ordered receipts. Existing E1 arithmetic, rank/select and fringe proofs are useful ingredients, but this is not already an E1 execution theorem.

**3. Close the uniform setup, width and state accounting.** The program is specialized by public n. Constant loads are charged, while deriving those n-only constants and constructing the instruction array happens before the query. A uniform theorem must either compute that metadata under its stated model or store and charge its reads. Prove bounds for every register, program operand, return PC and address. The current +1 tag needs a strict width bound for reachable logical words; arbitrary full-width all-ones logical words cannot carry that tag in the same word. Very small sizes also need care because the generic 4,444-instruction program cannot fit every small RC6 PC width.

The measured packed allocation excludes instruction storage and scratch registers. There are a fixed number of slots in this prototype, but the eventual combined theorem must state whether they are excluded machine state or add their O(log n) contribution to space. Register allocation and sharing should reduce the large prototype constants before publication. None of this requires pretending the current allocation already accounts for those slots.

These are now concrete follow-up obligations with an executed whole-query consumer. The experiment supports making this extension part of the preferred local maximum for v1. It does not support promising that the remaining proof is trivial or committing to a publication date before that work closes.

## Explicit limits

- No universal execution-correctness, width, compiler-correctness, or instruction-complexity theorem was proved.
- The executed canonical memories all have `LONG=0` and `SPARSE=0`. The comb fixture did not change that. Local stride is one in these sizes; the first logical word width permitting stride two is 98 bits. The affine formulas were challenged at nonzero formal counts, but this does not execute nonzero exception branches.
- The interior queries stay within one macroblock. Global/cross-macro selectors are compiled but were not exercised by these small canonical fixtures.
- Primitive widths, setup conventions and program/state accounting remain part of the next theorem, not consequences of the existing cell-probe capstone.
- This reports modeled instructions, not Lean/Python runtime or extracted native performance. Preprocessing complexity is unchanged and unproved.

## Evidence and reproduction

The core files are `ExportFixture.lean`, `physical_program.py`, `rank_select_program.py`, `lca_interior_program.py`, `machine.py`, `CheckMachine.lean`, `run_experiment.py` and `validate.py`. `fixture-*.json` contains canonical reference data; `*-vm.json` contains primitive execution receipts; `validation-results.json` records the wider query and mutation campaign. `program-n*.json` records the actual instruction arrays.

Run `./reproduce.ps1` to recompile the restricted programs, compare all reference cases, run the independent Lean interpreter and repeat the finite checks. Add `-RegenerateFixtures` to rebuild reference data from the exact RC6 source. The script accepts explicit Candidate/Lean/Python paths. Fixture generation is substantially slower than the VM checks. The script verifies the commit and tracked-source cleanliness before use.

The unchanged candidate's `lake build` passed; new Lean files elaborated and ran with Lean 4.22.0. Trust-base hygiene scans found none of the forbidden tokens in RMQ or the two new Lean files. Candidate `git diff --check` passed. The prior full RC6 aggregate gate was not repeated for this isolated experiment. The final reproduction log and package manifest accompany the report.

Source reconstruction anchors under RC6's `RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/`: `ReviewerController.lean:311` (attempted physical driver), `ReviewerWholeProtocol.lean:31` (whole query), `ReviewerLogicalLowering.lean:216` (physical plans), `ReviewerInteriorRead.lean:146` (ragged entry chunks), `ReviewerSparsePrelude.lean:197` (metadata reconstruction), and `ReviewerLogicalProtocol.lean:169` (rank geometry). The two focused specification notes in this directory provide detailed rank/select and interior equations.
