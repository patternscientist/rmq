# RC-6 whole-path reference fixture export

Owner: packed-architecture study agent. Source: `4639223bc8130b0ef752270b5cbdd74325abcd60`. Only `ExportFixture.lean` and this note are owned here. No candidate files were changed and no Lean/Lake process was launched by this agent.

The confirmed fixture is n=9 with input `[3,2,3,1,3,2,3,0,3]`, endpoints `[0,9)`, independent expected argmin index 7. `packedSummaryBlockSizeRaw n = 2*(log2 n+1)`, which is eight at n=9. The actual close endpoints are 4 and 17, in blocks zero and two, leaving a nonempty interior.

Run serially with the RC-6 compiled library:

```powershell
$env:LEAN_PATH = 'C:\Users\poin\Documents\RMQ\audit-rc6-20260910\.lake\build\lib\lean'
& 'C:\Users\poin\.elan\toolchains\leanprover--lean4---v4.22.0\bin\lean.exe' --run 'C:\Users\poin\Documents\RMQ\wordram-whole-path-spike-20260910\ExportFixture.lean' 'C:\Users\poin\Documents\RMQ\wordram-whole-path-spike-20260910\fixture-n9-balanced.json' 9 balanced
```

The extended CLI is `--run ExportFixture.lean OUTPUT N PATTERN [LEFT RIGHT]`; endpoints default to `[0,N)`. Supported patterns are `balanced` (periodic `[3,2,3,1,3,2,3,0]`), `ascending` (`i`), `descending` (`N-i`), `ties` (all three), and `zigzag` (even positions `N-i/2`, odd positions `-(i/2+1)`). Unknown pattern names fail explicitly. Decimal strings represent packed cell values and input integers without host-number precision assumptions.

The exporter writes JSON even on a consistency failure. **For the extended multi-query campaign, exit 0 and `coverage.accepted` mean the exported reference passes its consistency checks; `coverage.wholePathCovered` separately records the full different-block/interior/crossing criterion.** Thus a correct same-block or invalid query is an accepted reference without claiming full-path coverage. Exit 2 signals a consistency failure. Invalid ranges have the actual physical empty trace and a guarded empty logical replay with terminal `some none`.

`geometry` is evaluated from n only. Its eighteen `sourceDescriptors` follow canonical segment order `[17,18,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]`. `bitsLong1`, `bitsSparse1`, `countLong1` and `countSparse1` are *differences* from their zero-count bases. The exporter checks the resulting affine expressions against the real definitions at actual counts and all pairs from `{0,1,2,7}`. This finite check complements source inspection; it is not a universal affine proof. The VM must recover `longCount` and `sparseCount` from memory and charge the prefix arithmetic.

The eight interior descriptors contain entry count, entry width, word and bit prefixes, and component word count. All stored layout fields and derived layout fields are exported, together with rank/select/prelude sizes, chunk widths/counts and size-only directory/table overheads. These are compile-constant candidates; a final uniform theorem must account for their initialization convention.

`geometry.vmGlobals` supplies the lead DSL's names directly. `S` is blocks per superblock; `NB`/`NS` are block/sample counts; `M`/`MC` are macro size/count; `LC`/`GC` are local/global level counts; `RW`/`OW`/`BAW` are relative/offset/block-address widths. `LD`/`GD` are sparse-level table domains and `LW`/`GW` their entry widths. `OFF_*` are segment-20 logical word prefixes, and `OFF_DEAD` is that segment's total logical word count. All are n-only values from the existing definitions.

`reference` contains expected answers, actual content-dependent counts, physical traces and logical traces. It is checker data, **not VM input**. Each logical event records its protocol phase, full request (invocation, site, segment, index), optional decoded reply with exact bit width, and its expected physical plan. The logical replay uses the real `packedReviewerWholeNextRequest`/`ConsumeReply` and `packedReviewerLogicalRead` against the same packed memory. It does not create a second logical payload store. The full physical trace comes directly from `packedReviewerRunAgainstMemory`.

`wholePathCovered` requires both selects, left and right fringe phases, segment-20 interior reads, final rank, a crossing physical read and a nonempty middle-block range. Reference acceptance requires agreement between physical and logical terminals, the independent value-level leftmost argmin, exact whole-query physical-address expansion, every physical reply and its indexed memory cell, the affine geometry checks and no physical-run failure. The independent reference scan is defined in this exporter, uses strict value comparison and retains the earlier index on ties.

Source anchors: `ReviewerWholeProtocol.lean:31-102,130` supplies the logical machine; `ReviewerLogicalLowering.lean:216,251,368` supplies the actual plans, decode and physical-backed logical read; `ReviewerLcaProtocol.lean:65,167` separates same/different blocks and decides the nonempty middle; `ReadProgram.lean:800` fixes block size; `ReviewerController.lean:311,343` supplies the actual physical run. All paths are under `RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/`.

Execution result: the lead compiled and ran the exporter serially. I inspected `fixture-n9-balanced.json`: all thirteen coverage/consistency booleans are true, including `accepted`. The canonical allocation has **75 cells of 17 bits**, **1275 allocated bits**, **107 physical attempts** and **93 whole-query logical reads**. Both actual dynamic counts are zero (`longCount=0`, `sparseCount=0`); nonzero actual-header behavior is not covered by this fixture. The affine geometry formulas were additionally checked at all sixteen formal count pairs from `{0,1,2,7}`.

The logical phase counts are: left select 24, right select 18, left seed 4, left window 4, left fringe 9, middle 18, right seed 4, right window 4, right fringe 4 and final rank 4. Their sum is 93. The physical trace additionally includes the header and sparse prelude, and splits crossing logical reads into two cells. The canonical physical result and logical replay both return index 7, matching the independent scan. No VM instruction-cost claim follows from exporting this reference data.

The final compiler executes this n=9 balanced fixture in **107 physical reads and 57,223 charged instructions, cell width 17**. Both the Python VM and independent Lean interpreter reproduce that count and the ordered receipts. Earlier development counts were superseded after explicit operand snapshots and conditional lowering of Nat subtraction. This exporter supplies reference data and does not establish a universal RAM bound.

Expected coverage limit: a compact n=9/12/16 fixture exercises an interior range contained within one macroblock. Even a one-block interior goes through `packedReviewerInteriorStartLocalTwo`, which reads the local sparse-level table and local selectors before summary fields; it is not an uncharged direct minimum. A cross-macroblock/global-selector branch needs a much larger input and is not claimed merely from `interiorSegment20=true`. The JSON records every segment-20 index so the exact subcoverage remains reviewable.
