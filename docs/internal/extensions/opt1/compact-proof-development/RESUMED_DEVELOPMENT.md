# Resumed compact development evidence

Resume preflight passed at 8e355fda7788077f548865c1d6acf2ae5e88da55 against governance 0e6a00f654abc64f8b68988fa9675b9a839dca2f, actual runtime catalog rmq-coordinator/rmq-proof-sprint/rmq-audit-prompt, required rmq-proof-sprint. Root transferred the sole build slot after its focused Capstone repair; root also assigned routine Compact emitter repairs to this worker. Compact source needed no edit.

Kernel command results (each direct exact Lean 4.22.0 -j1 under the existing owned-process helper, 180-second deadline, 2 MiB output limit, task-local cache):
- Compact: PASS 12.803 seconds, no output.
- CompactProof first diagnostic: FAIL 13.141 seconds, three equal-PC normalization errors.
- CompactProof second diagnostic: FAIL 23.580 seconds, remaining prefix-length reassociation error.
- CompactProof after explicit arithmetic equalities: PASS 12.800 seconds, no output. Its full actual semantic, fuel, appended-halt, exact-type and small operational controls checked. All repaired goals concerned exact equalities between base+3+bodySize+1 and base+4+bodySize, or the three-instruction prefix length; signatures/premises/emitted code did not change.
- CompactSafety first diagnostic: FAIL 26.348 seconds, sole error in finite_agreement_does_not_give_fit: simp had reduced the goal to r≠2, so split had no target. Replaced the unnecessary split with omega. The main declarations reported no errors, but there is no successful module result until its final check.

Root requested slot transfer to source_relations after this first safety diagnostic. The last owned process exited, and the slot was explicitly transferred. No Lean is launched during static-worker ownership. Final CompactSafety and Axioms checks remain pending slot return.

Read-only query-consumer review at root request:
QueryProof's compact_compile_with_halt application specializes exactly to seq querySource (exit3), the emitted compactQueryProgram and the compactBound-derived budget; baseline and compact source projections match at arbitrary memory. Invalid result/read projections are correct. QuerySafety's hs projections match the generic output order and feed the same positional occurrence to run_read_fits. The old query_small_fields_fit is precisely 837572<capacity, so the strict code reduction supplies its end-PC bound. Canonical clauses consistently use buildMemory xs, initialState xs.length endpoints and wordWidth xs.length. No concrete defect was found by source inspection. Root still must kernel-check this composition; this review is not that verification.

Independent source_relations review of the final small controls confirms: inner repeat3(load) takes 15 instructions, outer repeat2(inner) takes 39, halt gives 40; emitted length 12; the first failed nested load is instruction 7 with one failed receipt; counter pairs 2/3 and 4/5 exclude source 0/1. Exact generic consumers project all semantic/safety conjuncts. This review ran no Lean.

Final explicit slot return: CompactSafety passed in 8.119 seconds and Axioms passed in 4.289 seconds. All generic declarations, exact-type consumers and local controls checked; only propext/Classical.choice/Quot.sound occur. The slot was immediately released to root. REPORT.md and final-leaf-checks.json supersede the earlier resource-wait status.
