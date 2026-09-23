# PQ1-RW frozen acceptance matrix

Governance: `4639223bc8130b0ef752270b5cbdd74325abcd60`. Exact assigned base: `067b6ffd350aee08f1496335ce957895f0da3fcc`. Canonical proof-sprint preflight PASS at that HEAD. Shared checkout; no staging/commits/shared-interface/shared-ledger changes. Frozen before source edits.

| ID | Verbatim requirement | Status/evidence |
| --- | --- | --- |
| REQ-RW-LOCATE | Derive (locateBlock8192).Safe from MetadataMatches shape regs and Data.Fits(wordWidth shape.size), for every segment/index in the input registers and every source status. Discharge regular/interior arithmetic, guards, subtraction non-underflow and positive divisors from the actual metadata. Cover all23 segments, every interior component, invalid huge representable indices, empty sentinels and absent words. Do not assume the desired location arithmetic bounds or source safety as hypotheses of the canonical theorem. | CLOSED — E1 canonical locator; E2 numerical envelope. All23 alternatives/every component; guarded invalid indices; every status. |
| REQ-RW-READER | Prove logicalReadBlock.Safe on shapeMemory with fitting input Data and canonical MetadataMatches only. All shifted bit addresses, multiplication/addition intermediates, span widths, raw returned cells and value+1 packet fit the same wordWidth. In particular zero-length sentinels may have positions beyond nominal memory bounds and must be handled honestly; absent logical words perform no physical load. Reuse spanBlock_safe, but derive every geometry premise from canonical location. A stronger arbitrary fitting-memory theorem is welcome but not a replacement for unconditional canonical instantiation. | CLOSED — E2/E3 complete canonical reader; packet/length and zero-sentinel capacity. No supplied safety/readiness premise. |
| REQ-RW-RUN | Prove FieldsFit for the actual fixed reader, including both dormant arms and resolved PCs, and derive actual Instruction.Safe for every indexed transition plus State.Fits for every fuel prefix on the same logicalReaderRun as logicalReaderRun_correct. Preserve exact packet, actual length, ordered readerReceipts, fixed1069 budget and caller frame. Give a List Int consumer starting from the charged metadata setup with fitting initialState, discharging metadata/value/width premises using existing setup proofs. No canonical source safety, read success, readiness, minimum size or rare-count-zero premise may remain. | CLOSED — E4/E5 same 1069 reader and actual348-setup/2-move input lineage; exact packet/length/ordered reads/frame/steps retained. |
| CHK-RW-LEAN | Narrow artifacts and independently spelled expected types; empty/singleton, absent segment, dead interior, empty sentinel and canonical crossing consumers or symbolic cases. Hygiene and whitespace checks; preserve the standard trust footprint. Every failed path that is claimed must retain the actual attempted address and fault status. | CLOSED — V1 final artifacts, independent imported types/axioms, permanent all-size/absence/dead/sentinel/crossing consumers; final hygiene/whitespace. |
| INV-WORD-WIDTH | stored and returned words fit one declared modeled machine word; | CLOSED — E3/E4/E6: loaded and returned values, all actual transition states and every prefix fit the identical wordWidth. |
| INV-ADDRESS-WIDTH | every executed address, dead/sentinel address, and encoded instruction operand fits the modeled machine word, not merely the host array bounds. Constructor-exhaustive evidence must include register identifiers, branch/jump targets, dormant code, and arithmetic operands; | CLOSED — E2/E4/E7: sentinel polynomial capacity, all dormant source fields/resolved targets, indexed actual address/reply bounds. |
| INV-WIDTH-SCALING | one query-independent word-width declaration bounds all stored words, addresses, sentinels, operands, and primitive results, and its capacity/width is related to input size in the form required by the public word-RAM claim. A standalone asymptotic fact about an unconstrained width function is insufficient. | CLOSED — E6 directly joins logarithmic wordWidth, counted shapeMemory, correct actual run and all-prefix fitting states. |
| INV-TRACE-EXECUTION | traces and footprints are derived from the execution they describe; | CLOSED — E4 names actual.transitions[index]? and run fuel prefixes; no trace-membership replacement. |
| INV-READ-BACKING | every successful read is backed positionally by the counted store; | CLOSED — E7 exact indexed occurrence yields receipt.reply = shapeMemory[receipt.address]? and width bounds. |
| INV-STORE-IDENTITY | the exact payload/store executed is the payload/store counted by the public space theorem; a theorem about a sibling payload is insufficient; | CLOSED — E6 counts exactly shapeMemory used by the value/safety run; E5 uses exactly buildMemory xs through setup/copies/reader. |
| INV-ALL-SIZE | exactness covers all assigned sizes and edge cases without hidden readiness or compatibility dispatch; | CLOSED — E1/E3/E5 quantify all shapes/lists; permanent empty/singleton/absent/dead/present-empty/crossing consumers. |
| INV-PROOF-SEPARATION | proof-only fields never carry answers or uncharged routing information; | CLOSED — E8 fixed code has no shape or semantic-store parameter; canonical reference and safety hypotheses occur only in proofs. |


## Verification plan

| Command | Role/coverage | Tree/runtime/deadline | Outcome |
| --- | --- | --- | --- |
| Direct ScalarSafety/ReaderSafety Lean target, then direct consumers | Development/final; all proof rows; abstraction-boundary proof and expected-type failures | Owned dirty sources on exact shared base; expect 5–30 s narrow checks, coordinate every check; inspect any timeout before retry | PASS — final artifacts/imported check; see V1 below |
| Repository trust/native scans and owned diff --check | Final; trust footprint and whitespace | Shared tree scan read-only, owned paths checked against absent-file base | PASS — final artifacts/imported check; see V1 below |

Root owns broad integrated Lake/gate/design-policy and committed-range certification. No replay campaign is assigned. Proofs must close complete canonical location and the actual 1069-fuel reader, including charged setup consumer; no supplied arithmetic-safety endpoint is accepted.


## Exact checked evidence

All source proofs have only their displayed assumptions. Full proposition inventory, code hashes, proof digestion, anti-vacuity challenges and design rationale are in PQ1_READER_SAFETY_REPORT.md. The blocks below quote exact checked propositions; row closure does not rely on declaration names alone.

### E1

```lean
theorem locateBlock_safe (base : Nat) (hb : 256 ≤ base) (shape : CartesianShape)
    (memory : Memory) (s : Data) (fit : s.Fits (wordWidth shape.size))
    (hm : MetadataMatches shape s.regs) :
    (locateBlock base).Safe memory (wordWidth shape.size) s
```

### E2

```lean
theorem reader_polynomial_fit (n : Nat) :
    175 * metadataEnvelope n + 2 * (metadataEnvelope n * metadataEnvelope n) <
      2 ^ wordWidth n
```

### E3

```lean
theorem logicalReadBlock_safe (shape : CartesianShape) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    logicalReadBlock.Safe (shapeMemory shape) (wordWidth shape.size) s
```

### E4

```lean
theorem logicalReaderRun_safe (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (fit : ∀ r, regs r < 2 ^ wordWidth shape.size) :
    let expected := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
      (regs 8192) (regs 8193)
    let actual := logicalReaderRun (shapeMemory shape) regs
    actual.result = some (logicalPacket expected) ∧
    actual.final.regs 8195 = logicalLength expected ∧
    actual.reads = readerReceipts shape (shapeMemory shape) (regs 8192) (regs 8193) ∧
    actual.steps ≤ 1069 ∧ ReaderFrame regs actual.final.regs ∧
    actual.final.Fits (wordWidth shape.size) ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe (wordWidth shape.size) t.before t.instruction ∧
        t.after.Fits (wordWidth shape.size)) ∧
    (∀ index, index ≤ 1069 →
      (run (shapeMemory shape) logicalReaderProgram index ⟨regs, 0, .running⟩).final.Fits
        (wordWidth shape.size))
```

### E5

```lean
theorem logicalReaderRun_from_initialState (xs : List Int) (segment index : Nat)
    (fit : (initialState xs.length segment index).Fits (wordWidth xs.length)) :
    let shape := SuccinctClassic.cartesianShape xs
    let regs := (readerInputRun xs segment index).final.regs
    let expected := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? segment index
    let actual := logicalReaderRun (buildMemory xs) regs
    actual.result = some (logicalPacket expected) ∧
    actual.final.regs 8195 = logicalLength expected ∧
    actual.reads = readerReceipts shape (buildMemory xs) segment index ∧
    actual.steps ≤ 1069 ∧ ReaderFrame regs actual.final.regs ∧
    actual.final.Fits (wordWidth xs.length) ∧
    (∀ (k : Nat) (t : Transition), actual.transitions[k]? = some t →
      Instruction.Safe (wordWidth xs.length) t.before t.instruction ∧
        t.after.Fits (wordWidth xs.length)) ∧
    (∀ k, k ≤ 1069 →
      (run (buildMemory xs) logicalReaderProgram k ⟨regs, 0, .running⟩).final.Fits
        (wordWidth xs.length))
```

### E6

```lean
theorem logicalReaderRun_allocation (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (fit : ∀ r, regs r < 2 ^ wordWidth shape.size) :
    (shapeMemory shape).length * wordWidth shape.size ≤
      2 * shape.size + allocationRho shape.size ∧
    wordWidth shape.size ≤ 192 * (Nat.log2 (shape.size + 2) + 1) ∧
    (∀ value ∈ shapeMemory shape, value < 2 ^ wordWidth shape.size) ∧
    (logicalReaderRun (shapeMemory shape) regs).result =
      some (logicalPacket ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        (regs 8192) (regs 8193))) ∧
    (∀ k, k ≤ 1069 →
      (run (shapeMemory shape) logicalReaderProgram k ⟨regs, 0, .running⟩).final.Fits
        (wordWidth shape.size))
```

### E7

```lean
theorem logicalReaderRun_read_fits (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (fit : ∀ r, regs r < 2 ^ wordWidth shape.size)
    (index : Nat) (t : Transition) (receipt : Receipt)
    (occurrence : (logicalReaderRun (shapeMemory shape) regs).transitions[index]? = some t)
    (read : t.receipt = some receipt) :
    receipt.address < 2 ^ wordWidth shape.size ∧
    receipt.reply = (shapeMemory shape)[receipt.address]? ∧
    (∀ value, receipt.reply = some value → value < 2 ^ wordWidth shape.size)
```

### E8 — identical code, memory and charged input lineage

`logicalReaderProgram = logicalReadBlock.compileAt 0 ++ [.halt 8194]` is fixed, with no shape/query-answer argument; `logicalReaderRun memory regs = run memory logicalReaderProgram 1069 ⟨regs,0,.running⟩`. Runtime metadata comes only from registers. The canonical proof chain is actual metadata -> actual locate output -> five actual prefix actions -> spanBlock8256 -> three suffix actions -> halt8194. Semantic stores occur only on theorem right-hand sides.

The List Int consumer uses `readerSetupRun xs segment index = run (buildMemory xs) (metadataSetupBlock.compileAt 0) 348 (initialState xs.length segment index)`, then `readerInputRun` executes the fixed two-move program on that actual final register bank, then the same logicalReaderRun uses the actual copied registers. The setup theorem supplies running status, all 174 actual installed fields, frame and fitting state. This is an explicitly staged run chain with entry PCs0, not an aggregate1419-step claim. Every stage names the identical buildMemory xs; allocation unfolds it to the shapeMemory in E6.

`logicalReaderProgram_fieldsFit` proves every instruction in the actual fixed program fits wordWidth n, covering dormant branches, arithmetic subtags, fixed register identifiers, resolved branch/jump PCs and appended halt. `logicalReadBlock_output_bounds` gives final packet≤2^oldWidth and length≤oldWidth, independently of fitting input; the main source-safe theorem consumes the strict logicalLength<wordWidth bound before packet tagging.

### Anti-vacuity checks

- E1/E3 retain arbitrary fitting register functions, all input segment/index values, every source status and all canonical shapes. No source Safe, arithmetic-bound, read-success, readiness, min-size or rare-count-zero hypothesis survives. Invalid huge fitting indices take executed guards before multiplication. Arithmetic helper assumptions are discharged from the real metadata in the canonical case/dispatch proofs.
- E2 bounds zero-length sentinel positions without assuming an array load or nominal allocation containment. empty_sentinel proves an actual packet 1/length 0/no-read run; absence and dead-interior consumers prove packet 0/no reads. singleton_all_requests retains arbitrary fitting segment/index values.
- canonical_crossing retains the actual two raw addresses, successful backing replies and ordered two-receipt list. E7 retains an exact transition position and receipt identity, so a repeated equal receipt cannot replace its producer. No failed canonical path is claimed; the reusable arbitrary-memory body safety proof covers the real span decoder's fault exit, while LoadSafety supplies its already checked failed-load provenance consumers.
- E6 joins the literal counted memory, declared logarithmic width, correct actual reply and all-prefix state fit. It excludes sibling-store substitution and unconstrained-width claims. No mutation/replay campaign is assigned or claimed.

### V1 — final verification

- ScalarSafety clean artifact PASS 3.8277913s; SHA256 `574234fe2817a428c24b324c53775d301c4140d509b10b06bac59975373eac48`.
- ReaderSafety clean complete artifact PASS 10.674946s; SHA256 `d9c17e4c48f95df2ca3ff95c18de82c5f8f535328f8916b14f12f35d6a8716ec`.
- Imported independently spelled expected source/prefix types and 7 axiom inventories PASS 4.1799044s; only propext/Classical.choice/Quot.sound. Permanent run_expectedType also spells actual indexed instruction safety/read equality on the concrete1069 program.
- Final repository trust/native scans: no matches (chunk 677a56). Owned tracked/no-index whitespace checks: PASS, with only ordinary LF-to-CRLF notices (chunk 225e85). All 12 stable rows are unique/CLOSED and all 4 prompt requirements match verbatim (chunk a793a0). Broad integration gates remain root-owned; no full Lake/gate was launched.

Status: CANDIDATE_COMPLETE. I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.
