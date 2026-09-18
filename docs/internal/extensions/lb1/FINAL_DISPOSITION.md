# LB-1 final evidence disposition

Implementation target: 5033ce54da233fc7a3df319d50ab09a2ebee523a.
Frozen contract: 0bbbe8ca4a937bc9782b2f7c5cc5419faa1a75a2.
The 29 entire rows in ACCEPTANCE_MATRIX.md remain byte-identical, excluding
only their LF/CRLF delimiters. This separate evidence ledger does not change
requirements or record coordinator acceptance. EVIDENCE_PLAN.md supplies the
expanded propositions, guards and object-composition chains for the compact
entries below; FINAL_AUDIT.md independently reconstructs the exact requirements.

All locally assigned proof/consumer and finite mutation/runtime checks below have checked source and successful exact-target execution evidence. Final worker status is BLOCKED on coordinator-owned full build/aggregate results; none of these entries is coordinator acceptance. The independent audit found no source/model defect and leaves external certification separate.

In the table, O01..O16 and M01..M33 refer to the version-3 replay identifiers
and their corresponding independently typed checkO/checkM declarations.
Runtime R01..R06 refer to the actual allocation decoder/serializer fixtures.
The complete raw records and exact-stage verifier are indexed by
evidence/final-evidence-manifest.json. All entries remain subject to the
coordinator-owned broad certification and acceptance disposition.

| Frozen ID | Exact proposition/object evidence and recorded adversarial coverage |
| --- | --- |
| REQ-LB-COUNT | Bounded strings have Nodup, cardinality `2^(B+1)-1`, membership iff length<=B; fixed exact encoder gives shape injection and `doubledLogSlackLower n <= 2*(B+1)`. Separate generic consumer; G01/G02 reject weakening lower/exactness; checked all-size/advice/tiny witnesses. |
| REQ-LB-PQ1 | Whole finite-word inverse at positive fixed width; `length(allocationBits xs)=length(buildMemory xs)*wordWidth xs.length`; full reconstructed-memory equality; exact total half-open decoder from bits/n/endpoints only; shape representative injection and intentional same-shape sharing. O01..O08, D01..D03, F01, S01; R01..R06. |
| REQ-LB-MODEL | `UniformAllocationBudget n B` quantifies all size-n inputs; actual `allocationEncoding n B budget` feeds arbitrary-B count/lower and canonical `2*n+allocationRho n`, whose residual is LittleOLinear. O09..O14 and S03; M01..M14 pin separate complete-capacity/width/program/scratch facts. |
| REQ-LB-CONSUMER | publicContract/composedConsumer and canonicalEncodingConsumer consume actual allocationBits/allocationDecoder and the generic lower theorem; literal predicate pins fix all underlying objects and guards. P01/G01/G02, all 49 O/M attacks, F01/F02/S01/S02/S03/H01. |
| CHK-LB-CONTROLS | Kernel empty/singleton, tie, null/wrong decoder, all-size, zero-budget and size-only/fixed-input-shape-advice propositions; R01..R06 actual fixtures; G02/D01/D02/D03 target original exactness/serialization equations; A01/A02 expected-accept controls. |
| REPLAY-EXACT-REGISTRY | Literal runner list and version 3 JSON must equal all 63 ordered unique IDs; summary independently checked against that literal order,61 REJECT/2 ACCEPT; missing/duplicate/empty controls and 6 runtime IDs. |
| REPLAY-SELECTOR-NONVACUITY | Actual omitted/valid/empty/whitespace/malformed/unknown boundaries for replay and runtime; two external simultaneous CLI/environment probes and a malformed runtime ID inside a valid channel reject before any case pass. Exact focused mode receipts retain exits/output/deadlines. |
| REPLAY-SUBPROCESS-DEADLINE | Existing owned-tree helper bounds each child; raw stdout/stderr/exits retained; source/olean byte restoration and clean state after each case/finally. Windows descendant probe requires a created child and its absence afterward; POSIX is UNOBSERVED, never reported passed. |
| INV-STORE-IDENTITY | Serialized length and whole memory recovery plus every-fuel run equality concern identical buildMemory/reconstructedMemory; O03/O04/O15, F01/S01/S02 reject sibling facts. |
| INV-VALUE-DEPENDENCY | Decoder definition reads reconstructed numeric words through queryNat/fixed primitive program; load writes the actual destination register and result comes from run state. Exact scanWindow is the semantic conclusion, not an executable oracle. D01/D02 and O05/O06/M16..M19/M31. |
| INV-SEMANTIC-NONVACUITY | Actual operational decoder and all-size positive-window domain; replicate witness for every n; universal exactness cannot become empty-input-only. O05, H01 and generic exactness/advice controls. |
| INV-TRACE-EXECUTION | M27 pins occurrence index, producing load, folded pre-state and execute transition; M28 pins ordered reads from that same run. No new trace constructor; M27/M28 and F02 reject weakening/deletion. |
| INV-STORE-AGREEMENT | Agreement at actual receipt addresses implies equality of whole runs with same program, budget and initialState, preserving result/cost/trace. Literal M30 consumer and mutation. |
| INV-READ-BACKING | Every indexed successful load reply equals reconstructedMemory at its actual address; word/address bounds retain guards; no failed canonical loads. M26/M27/M32 and F02. |
| INV-WORD-WIDTH | Every reconstructed word, modeled result/state and prefix fits the same n-only width under original endpoint premises. M03/M06/M23..M26. |
| INV-ADDRESS-WIDTH | Allocation address capacity includes end sentinel; encoded instruction bounds cover dormant operands; every actual guarded transition/prefix/load fits. M07/M08/M24..M26. |
| INV-INSTRUCTION-ATOMICITY | Unchanged fixed PQ1 primitive execute/run is transported by complete store equality; conversions are outside the charged primitive profile. M15..M28 types and source expansion preserve the declared primitive vocabulary. |
| INV-PROGRAM-ACCOUNTING | Complete capacity counts actual memory plus flattened queryProgram encoding plus finite registers/scratch at the same width; shape metadata remains in counted memory. M05/M08/M10..M14, including unused-register prefixes. |
| INV-ORACLE-INDEPENDENCE | Actual allocationDecoder runtime results are compared with independent literal empty/singleton/tie expectations; zero-word and same-shape fixtures use direct serializer/memory identities. R01..R06; semantic references are not implementation-derived expected values. |
| INV-VALIDATION-REACH | Validation imports actual allocation layer, independently pins and executes allocationBits/reconstructedMemory/allocationDecoder; fresh baseline consumer compilation, public dependency mutation and 6 runtime cases. |
| INV-ALL-SIZE | Generic and canonical encodings exist for every n; decoder exactness covers every ordinary xs with original ValidRange, including tiny/invalid cases without readiness dispatch. H01/R01/R02 plus all-size and empty/singleton kernel witnesses. |
| INV-PROOF-SEPARATION | Decoder captures only public n, bits and endpoints; no xs/shape/proof answer parameter; primitive returned value follows counted loads. Advice positive/negative controls and D01/D02; A02 harmless unused proof note accepted. |
| INV-NO-SYNTHETIC | Entire recovered-memory run equals existing primitive run; receipt/ordered-refinement facts derive from actual execution with occurrence positions. O15/M27/M28, S02/F02; no decorative replay introduced. |
| INV-CATEGORY-SEPARATION | Payload lengths, numeric memory, fixed code, scratch, proofs, model steps and measured runtime remain distinct. O03/O13/M05/M09/M21/M22; bit conversion has no charged-time claim. |
| INV-PUBLIC-COMPOSITION | Generic canonical instance plus exact decoder and whole memory/run identity compose in the public capstone and typed consumer; every machine projection uses recovered identical memory and retained guards. P01/G01/O04/O15/S01/S02/S03/H01. |
| INV-CERTIFICATE-ANTI-BYPASS | Actual parent-free 4/16/33 metadata and literal49 projected expected types; all 49 weakened producers compile, then corresponding named consumer fails; field deletions/sibling substitutions/public proposition attacks test additional bypasses. A01/A02 establish expected-accept behavior. |
| INV-MUTATION-REPRODUCIBILITY | Committed version 3 registry and runner replay all 63 expected verdicts with exact diagnostics, owned bounds and restoration; independent raw-stage reconciliation plus source identity; original inconclusive campaign retained separately. |
| INV-GLOBAL-PHYSICAL-MACHINE | Full buildMemory is serialized/recovered before execution; all program segments run on that one numeric store and same width. Entire fuel-run equality and all 33 transported fields, especially M05/M07/M08/M24..M30, preserve complete footprint. |
| INV-WIDTH-SCALING | Single width depends only on n, lies between log2(n+2)+1 and 192 times that quantity, and binds actual store, addresses, encoded operands and guarded transitions. M03/M06/M07/M08/M23..M26, linked through whole-store recovery. |

Final local outcomes:63/63 version 3 cases (61 REJECT,2 ACCEPT),134 exact stages,6/6 full runtime IDs,5/5 focused mode entry points,3/3 additional selector branches,20/20 named axiom records,2/2 zero-hit trust source scans,29 unchanged frozen rows with 7 corruption controls. Full saved-evidence reconciliation reports EVIDENCE_CONSISTENT. Source-target policy checks passed; actual report-tree checks are recorded separately in evidence/report-checks.json. The independent report is FINAL_AUDIT.md.

No mathematical obstruction is asserted. Broad certification is an external
required result explicitly assigned to the coordinator. Physical POSIX timeout
ownership remains unobserved on this Windows host; the frozen requirement
requires that limitation to be reported, not converted into a passed test.
