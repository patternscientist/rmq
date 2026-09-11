Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

PQ1-RW, branch `codex/fully-charged-packed-query-v1`, shared worktree `C:/Users/poin/.codex/worktrees/a84a/RMQ`. Assigned base `067b6ffd350aee08f1496335ce957895f0da3fcc`; governance `4639223bc8130b0ef752270b5cbdd74325abcd60`. Canonical proof-sprint preflight passed; the 12-row matrix was frozen before edits. No staging, commits, shared-ledger edits, or edits to shared source interfaces.

## Scope and composition

Only ReaderSafety.lean, ScalarSafety.lean, and this leaf's matrix/report are owned. The complete reader is the endpoint. Root owns full-query safety, integration, public claim updates and aggregate gates. All four collaboration slots already carried disjoint useful work, so this sequential compiler/reader consumer leaf did not spawn ceremonial subagents.

Let E = metadataEnvelope n = 64*(2^oldWidth)^2. The checked bound `175*E + 2*(E*E) < 2^wordWidth n` covers locator products, accumulated positions, the 174-word metadata prefix, and all zero-length sentinel positions. The bound follows from `256*E^2 = 2^(20+4*oldWidth)` and `wordWidth n = 32+8*oldWidth`; there is no array-presence premise. Valid-index guards bound regular products and both interior products by E^2. Canonical chunk divisors are positive because canonical entry widths and BP width are positive and ceiling-division capacity covers the entry.

ScalarChecks removes repeated copies of the all-register invariant inside a proof only. Its structural preservation theorem restores the actual Block.Safe judgment. SimpleScalar handles only fixed constants, moves and comparisons. Arithmetic safety is checked at each evaluated operation. The source interpreter, ISA, field encoding, metadata and allocation are unchanged.

The canonical source chain is MetadataMatches + Data.Fits -> locateBlock.Safe -> readSpanPrefix.Safe -> spanBlock_safe on the actual evaluated prefix registers -> readSpanSuffix.Safe -> logicalReadBlock.Safe. The span proof accepts faults on arbitrary fitting numeric memory; canonical source value correctness independently proves the canonical allocation's successful logical replies. A logical absence takes the no-load branch. A present empty sentinel returns packet 1 and length 0 with no raw reads. Packet tagging applies after logical decoding; the decoded value is below 2^logicalLength and logicalLength<wordWidth.

The actual execution chain combines logicalReadBlock_safe with Block.compile_with_halt_safe and logicalReaderRun_correct, using the identical memory, registers, fixed compiled program and fuel 1069 in every conjunct. It preserves packet, actual length, ordered receipts, caller frame and actual step bound, then adds indexed Instruction.Safe and every-fuel-prefix State.Fits. The static FieldsFit proof covers all dormant arms and the appended halt; compile_fits resolves target PCs.

The List Int consumer follows actual standalone executions: readerSetupRun runs the fixed348-budget metadata program from fitting initialState; readerInputRun runs two charged moves using that actual final register bank; logicalReaderRun then runs the fixed 1069-budget reader on those actual copied registers. The setup theorem proves the status is running before the next standalone program begins. These are explicitly staged runs with entry PC0, not a claimed aggregate1419-instruction theorem. All three use the same buildMemory xs. No ghost metadata installation or proof-computed request register bank is substituted for a charged step.

## Checked proposition inventory

The following exact propositions are checked in the emitted final artifacts. Quantified inputs and conclusions are retained; theorem names alone are not the evidence.

### reader_polynomial_fit

```lean
theorem reader_polynomial_fit (n : Nat) :
    175 * metadataEnvelope n + 2 * (metadataEnvelope n * metadataEnvelope n) <
      2 ^ wordWidth n
```

### locateBlock_safe

```lean
theorem locateBlock_safe (base : Nat) (hb : 256 ≤ base) (shape : CartesianShape)
    (memory : Memory) (s : Data) (fit : s.Fits (wordWidth shape.size))
    (hm : MetadataMatches shape s.regs) :
    (locateBlock base).Safe memory (wordWidth shape.size) s
```

### readSpanBody_safe

```lean
theorem readSpanBody_safe (memory : Memory) (width : Nat) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits width) (hw : 8 ≤ width)
    (memoryFit : MemoryWordsFit memory width) (hwidth : regs 22 = width)
    (position : 174 * width + regs 8195 < 2 ^ width) (length : regs 8196 < width) :
    readSpanBody.Safe memory width ⟨regs, .running⟩
```

### logicalReadBlock_safe

```lean
theorem logicalReadBlock_safe (shape : CartesianShape) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    logicalReadBlock.Safe (shapeMemory shape) (wordWidth shape.size) s
```

### logicalReadBlock_output_bounds

```lean
theorem logicalReadBlock_output_bounds (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) :
    let actual := logicalReadBlock.eval (shapeMemory shape) ⟨regs, .running⟩
    actual.final.regs 8194 ≤ 2 ^ packedReviewerCellWidth shape.size ∧
    actual.final.regs 8195 ≤ packedReviewerCellWidth shape.size
```

### logicalReaderProgram_fieldsFit

```lean
theorem logicalReaderProgram_fieldsFit (n : Nat) :
    ∀ instruction ∈ logicalReaderProgram, instruction.Fits (wordWidth n)
```

### logicalReaderRun_safe

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

### readerInputMoves_run

```lean
theorem readerInputMoves_run (shape : CartesianShape) (memory : Memory) (n : Nat) (regs : Registers)
    (segment index : Nat) (mf : MetadataMatches shape regs)
    (rf : ∀ r, regs r < 2 ^ wordWidth n)
    (i0 : regs 0 = segment) (i1 : regs 1 = index) :
    let actual := run memory (readerInputMoves.compileAt 0) 2 ⟨regs, 0, .running⟩
    MetadataMatches shape actual.final.regs ∧
    (∀ r, actual.final.regs r < 2 ^ wordWidth n) ∧
    actual.final.regs 8192 = segment ∧ actual.final.regs 8193 = index ∧
    actual.reads = [] ∧ actual.steps ≤ 2 ∧
    (∀ k, k ≤ 2 → (run memory (readerInputMoves.compileAt 0) k
      ⟨regs, 0, .running⟩).final.Fits (wordWidth n))
```

### readerInputRun_prepared

```lean
theorem readerInputRun_prepared (xs : List Int) (segment index : Nat)
    (fit : (initialState xs.length segment index).Fits (wordWidth xs.length)) :
    let actual := readerInputRun xs segment index
    MetadataMatches (SuccinctClassic.cartesianShape xs) actual.final.regs ∧
    (∀ r, actual.final.regs r < 2 ^ wordWidth xs.length) ∧
    actual.final.regs 8192 = segment ∧ actual.final.regs 8193 = index ∧
    actual.reads = [] ∧ actual.steps ≤ 2 ∧
    (∀ k, k ≤ 2 →
      (run (buildMemory xs) (readerInputMoves.compileAt 0) k
        ⟨(run (buildMemory xs) (metadataSetupBlock.compileAt 0) 348 (initialState xs.length segment index)).final.regs, 0, .running⟩).final.Fits
          (wordWidth xs.length))
```

### logicalReaderRun_from_initialState

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

### logicalReaderRun_allocation

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

### logicalReaderRun_read_fits

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

## Anti-vacuity and scope challenges

- The canonical conclusions accept any fitting initial register function and every status; they do not assume Safe, arithmetic products, presence, readiness, a minimum size, or a vanishing exceptional count. The generic arithmetic helper premises are discharged in regularCaseBlock_safe/interiorCaseBlock_safe from actual metadata. source_expectedType spells the canonical quantifiers independently.
- Huge fitting indices are rejected by executed guards before dangerous products. All23 regular alternatives and every interior component occur in fixed syntax; static fit does not discard dormant arms.
- Empty sentinels retain a capacity proof for the computed position even though no read occurs. The bound is deliberately independent of nominal allocation-end containment.
- Every receipt is tied to an indexed actual transition, its actual instruction and pre-state through run_read_fits, so a repeated equal receipt cannot replace the producing occurrence. raw reply equality names exactly shapeMemory shape at the actual address.
- Empty/singleton, absent segment, dead interior, present empty sentinel and symbolic canonical crossing are permanent consumers. The crossing theorem names both successful actual replies and their actual addresses in order. No mutation campaign is claimed.

## Proposed design rationale for the lead

The numerical envelope and source-only ReaderSafe interface are proof abstractions consumed by the existing compiler safety theorem. A sharp per-table arithmetic proof was unnecessary: existing counted metadata bounds and executed guards give a uniform envelope that also handles empty sentinels. Repeating all-register fit throughout full evaluator simplification was rejected after the loader experience; ScalarChecks plus small source summaries preserves the same final proposition. Literal evaluator reduction in the setup-copy consumer was replaced by a generic copy-run theorem over abstract registers, then instantiated with the actual charged setup output. No process-policy decision or source/program model change was made. Root owns any shared ledger append and public claim synchronization.

## Proof digestion

Conceptually, safe machine words now survive the entire physical logical-word reader: descriptor selection, guarded arithmetic, shifted physical addressing, one/two raw loads, fragment arithmetic and final tagging. In plain English, the same checked reader that returns the right logical word and ordered raw reads also keeps every executed instruction and every intermediate machine state within the declared word width. Live assumptions are exactly canonical metadata and fitting input data, or fitting initialState for the charged-setup consumer. The fixed word width is query independent and remains tied to size by the existing allocation/width theorems.

A skeptical reader should examine whether an invalid index can reach multiplication, whether an empty sentinel evades address capacity, whether the tagged value is a raw full physical cell, and whether all returned safety facts describe the same executed allocation and indexed trace. The permanent consumers and the exact canonical theorem propositions address those questions. The remaining larger question is full-controller arithmetic outside this reader, owned by root.

## Verification

Final unchanged source bytes:
- ScalarSafety SHA256 `574234fe2817a428c24b324c53775d301c4140d509b10b06bac59975373eac48`; clean `-o/-i` PASS 3.8277913 seconds (tool chunk 8f72a0).
- ReaderSafety SHA256 `d9c17e4c48f95df2ca3ff95c18de82c5f8f535328f8916b14f12f35d6a8716ec`; clean complete `-o/-i` PASS 10.674946 seconds (chunks f3fcfb/d580c4).
- Imported independently spelled source and every-prefix expected types, plus 7 axiom inventories: PASS 4.1799044 seconds (chunk 5d5609). The checked declarations depend only on `propext`, `Classical.choice`, `Quot.sound`. The temporary imported check first had a namespace typo; correcting its CartesianShape qualification produced the final pass without source edits.
- Permanent consumers in ReaderSafety: source_expectedType, run_expectedType, absent_request, absent_segment, dead_interior, empty_sentinel, singleton_all_requests, canonical_crossing. The empty sentinel proves packet 1, length 0 and no reads; the crossing consumer names both successful replies and their raw addresses in exact order. logicalReaderRun_read_fits fixes the producing transition index and raw backing equality.
- Repository-wide trust/native scans: no matches (chunk 677a56). Owned tracked/no-index whitespace checks: PASS, with normal LF-to-CRLF notices (chunk 225e85). All 12 stable IDs are unique/CLOSED and the 4 prompt requirements match verbatim (chunk a793a0). Current shared HEAD remains the assigned base 067b6ffd350aee08f1496335ce957895f0da3fcc. No broad Lake/gate run, mutation campaign, native-decision proof, staging or commit was performed.

The initial bounded core passed14.2774 seconds. Subsequent full diagnostics exposed reducible projection/simplification at the concrete setup boundary, then a width-index annotation. The final proof moves rewrites into generic lemmas over abstract registers and passes the size index separately before substituting actual run outputs. This reduced the final full ReaderSafety check to10.675 seconds. No unchanged expensive retry or increased heartbeat budget was used.

Broad gates are root-owned and disproportionate for this narrow leaf. Root retains responsibility for shared-ledger/public-claim integration and independent acceptance; this report records only CANDIDATE_COMPLETE.
