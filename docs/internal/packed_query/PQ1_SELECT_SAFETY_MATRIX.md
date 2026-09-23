# PQ1-SS frozen acceptance matrix

Frozen before implementation. Base/HEAD `067b6ffd350aee08f1496335ce957895f0da3fcc`;
governance `4639223bc8130b0ef752270b5cbdd74325abcd60`.
Preflight PASS for `rmq-proof-sprint` with runtime project catalog
`rmq-coordinator,rmq-proof-sprint,rmq-audit-prompt`.
Shared worktree `C:/Users/poin/.codex/worktrees/a84a/RMQ`; branch
`codex/fully-charged-packed-query-v1`. Own SelectSafety and this matrix/report;
SelectSource changes require same-order factoring or a formally justified repair
coordinated with the lead. No shared-ledger edits, staging or commits.

| ID | Exact frozen requirement | Scope | Evidence needed | Named consumer / exact composition chain | Anti-vacuity challenge planned / outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `REQ-SS-WORD` | Prove every scalar action of selectWordBlock and all eight guarded copies safe from canonical metadata, fitting registers, bounded logical word/length and bounded occurrence. Prove chunk shifts, rank/select table slot polynomials, decoding, cumulative counts and result packet increment at the fixed wordWidth; absent replies retain existing semantics. | Select controller safety on the canonical allocation | Complete source Safe and actual-run Instruction.Safe/all-prefix Fits at fixed wordWidth, exact value/reads/budget and output bound | ReaderSafety + independent scalar/entry/word leaves + RankSafety + SelectProof -> fixed select source -> Safety.Compiler -> same canonical run | PASS: checked canonical_boundary/empty_shape and symbolic_rare_paths; the expanded run_expectedType fixes the actual program, memory, index and width. No mutation campaign claimed. | E-WORD and E-STATIC quote the complete source, output-envelope and actual 17754-fuel appended-halt word safety types. Eight guarded copies are covered by the checked invariant induction. | Closed — checked final source; coordinator acceptance pending |
| `REQ-SS-CLOSE` | Prove selectCloseBlock logicalReadBlock Safe on shapeMemory for fitting registers, canonical MetadataMatches and occurrence at most shape.size. Cover all super/local entry reads, long/sparse branches, dense first/second-word route, all missing cases and small inputs. Derive every needed metadata positivity and address/result bound; no readiness, rare-count-zero, source-safety or successful-read assumption. | Select controller safety on the canonical allocation | Complete source Safe and actual-run Instruction.Safe/all-prefix Fits at fixed wordWidth, exact value/reads/budget and output bound | ReaderSafety + independent scalar/entry/word leaves + RankSafety + SelectProof -> fixed select source -> Safety.Compiler -> same canonical run | PASS: checked canonical_boundary/empty_shape and symbolic_rare_paths; the expanded run_expectedType fixes the actual program, memory, index and width. No mutation campaign claimed. | E-CLOSE quotes canonical Safe for arbitrary fitting Data and metadata, with no occurrence restriction; the bounded requested domain is consumed by source_expectedType. Packet≤2n and packet≤E are universal. | Closed — checked final source; coordinator acceptance pending |
| `REQ-SS-RUN` | Consume completed RankSafety wrapper source safety and RankProof/SelectProof value/frame results to prove canonical full select source and actual compiled appended-halt run safety with exact same result, ordered physical receipts and fixed budget. Prove all static encoded fields including dormant arms and PCs fit; every indexed transition is Instruction.Safe and every fuel prefix State.Fits. Expose final packet bound and source interface for full query. | Select controller safety on the canonical allocation | Complete source Safe and actual-run Instruction.Safe/all-prefix Fits at fixed wordWidth, exact value/reads/budget and output bound | ReaderSafety + independent scalar/entry/word leaves + RankSafety + SelectProof -> fixed select source -> Safety.Compiler -> same canonical run | PASS: checked canonical_boundary/empty_shape and symbolic_rare_paths; the expanded run_expectedType fixes the actual program, memory, index and width. No mutation campaign claimed. | E-RUN quotes the same canonical 91243-fuel result/status/ordered reads/frame/budget, all encoded fields, every indexed safe transition and every fitting fuel prefix, plus indexed read backing. E-CLOSE exposes the packet bounds for the full query. | Closed — checked final source; coordinator acceptance pending |
| `CHK-SS-LEAN` | Narrow artifact plus independently spelled expected-type consumers, empty and canonical occurrence boundary cases and universal symbolic rare paths. Standard trust inventory, hygiene and whitespace checks; quote full propositions and actual object-composition chains. | Select controller safety on the canonical allocation | Complete source Safe and actual-run Instruction.Safe/all-prefix Fits at fixed wordWidth, exact value/reads/budget and output bound | ReaderSafety + independent scalar/entry/word leaves + RankSafety + SelectProof -> fixed select source -> Safety.Compiler -> same canonical run | PASS: checked canonical_boundary/empty_shape and symbolic_rare_paths; the expanded run_expectedType fixes the actual program, memory, index and width. No mutation campaign claimed. | E-BOUNDARY and E-RARE quote checked empty/boundary and universal rare-route consumers; E-RUN is independently restated in an imported Lean consumer. Final source and imported checks are clean; fourteen trust inventories and both scans pass. | Closed — checked final source; coordinator acceptance pending |
| `INV-WORD-WIDTH` | stored and returned words fit one declared modeled machine word; | Select controller safety on the canonical allocation | Complete source Safe and actual-run Instruction.Safe/all-prefix Fits at fixed wordWidth, exact value/reads/budget and output bound | ReaderSafety + independent scalar/entry/word leaves + RankSafety + SelectProof -> fixed select source -> Safety.Compiler -> same canonical run | PASS: checked canonical_boundary/empty_shape and symbolic_rare_paths; the expanded run_expectedType fixes the actual program, memory, index and width. No mutation campaign claimed. | E-RUN requires final packet<2^wordWidth, Instruction.Safe at every transition and State.Fits for every prefix; E-ALLOCATION quantifies all stored words at this same width. | Closed — checked final source; coordinator acceptance pending |
| `INV-ADDRESS-WIDTH` | every executed address, dead/sentinel address, and encoded instruction operand fits the modeled machine word, not merely the host array bounds. Constructor-exhaustive evidence must include register identifiers, branch/jump targets, dormant code, and arithmetic operands; | Select controller safety on the canonical allocation | Complete source Safe and actual-run Instruction.Safe/all-prefix Fits at fixed wordWidth, exact value/reads/budget and output bound | ReaderSafety + independent scalar/entry/word leaves + RankSafety + SelectProof -> fixed select source -> Safety.Compiler -> same canonical run | PASS: checked canonical_boundary/empty_shape and symbolic_rare_paths; the expanded run_expectedType fixes the actual program, memory, index and width. No mutation campaign claimed. | E-STATIC covers every source field and compiled instruction including dormant arms/targets. E-RUN quantifies each producing transition index, receipt address<2^wordWidth and actual memory lookup; missing attempts remain included. | Closed — checked final source; coordinator acceptance pending |
| `INV-WIDTH-SCALING` | one query-independent word-width declaration bounds all stored words, addresses, sentinels, operands, and primitive results, and its capacity/width is related to input size in the form required by the public word-RAM claim. A standalone asymptotic fact about an unconstrained width function is insufficient. | Select controller safety on the canonical allocation | Complete source Safe and actual-run Instruction.Safe/all-prefix Fits at fixed wordWidth, exact value/reads/budget and output bound | ReaderSafety + independent scalar/entry/word leaves + RankSafety + SelectProof -> fixed select source -> Safety.Compiler -> same canonical run | PASS: checked canonical_boundary/empty_shape and symbolic_rare_paths; the expanded run_expectedType fixes the actual program, memory, index and width. No mutation campaign claimed. | E-ALLOCATION combines this exact select run and its entire execution-safety predicate with wordWidth≤ 192*(log2(size+2)+1), counted space and fitting stored words. The width is fixed by size, not the query. | Closed — checked final source; coordinator acceptance pending |
| `INV-TRACE-EXECUTION` | traces and footprints are derived from the execution they describe; | Select controller safety on the canonical allocation | Complete source Safe and actual-run Instruction.Safe/all-prefix Fits at fixed wordWidth, exact value/reads/budget and output bound | ReaderSafety + independent scalar/entry/word leaves + RankSafety + SelectProof -> fixed select source -> Safety.Compiler -> same canonical run | PASS: checked canonical_boundary/empty_shape and symbolic_rare_paths; the expanded run_expectedType fixes the actual program, memory, index and width. No mutation campaign claimed. | E-RUN equates actual.reads to the reference trace flatMap of the canonical reader receipts for this same run; its safety observations use actual.transitions[index]?=some t. | Closed — checked final source; coordinator acceptance pending |
| `INV-READ-BACKING` | every successful read is backed positionally by the counted store; | Select controller safety on the canonical allocation | Complete source Safe and actual-run Instruction.Safe/all-prefix Fits at fixed wordWidth, exact value/reads/budget and output bound | ReaderSafety + independent scalar/entry/word leaves + RankSafety + SelectProof -> fixed select source -> Safety.Compiler -> same canonical run | PASS: checked canonical_boundary/empty_shape and symbolic_rare_paths; the expanded run_expectedType fixes the actual program, memory, index and width. No mutation campaign claimed. | E-RUN quantifies every indexed producing transition/receipt and proves receipt.reply=(shapeMemory shape)[receipt.address]? plus fitting successful values; multiplicity and positions are preserved. | Closed — checked final source; coordinator acceptance pending |
| `INV-STORE-IDENTITY` | the exact payload/store executed is the payload/store counted by the public space theorem; a theorem about a sibling payload is insufficient; | Select controller safety on the canonical allocation | Complete source Safe and actual-run Instruction.Safe/all-prefix Fits at fixed wordWidth, exact value/reads/budget and output bound | ReaderSafety + independent scalar/entry/word leaves + RankSafety + SelectProof -> fixed select source -> Safety.Compiler -> same canonical run | PASS: checked canonical_boundary/empty_shape and symbolic_rare_paths; the expanded run_expectedType fixes the actual program, memory, index and width. No mutation campaign claimed. | E-ALLOCATION quotes shapeMemory length*wordWidth≤2*size+allocationRho together with the result and execution safety of selectCloseRun on that identical shapeMemory. | Closed — checked final source; coordinator acceptance pending |
| `INV-ALL-SIZE` | exactness covers all assigned sizes and edge cases without hidden readiness or compatibility dispatch; | Select controller safety on the canonical allocation | Complete source Safe and actual-run Instruction.Safe/all-prefix Fits at fixed wordWidth, exact value/reads/budget and output bound | ReaderSafety + independent scalar/entry/word leaves + RankSafety + SelectProof -> fixed select source -> Safety.Compiler -> same canonical run | PASS: checked canonical_boundary/empty_shape and symbolic_rare_paths; the expanded run_expectedType fixes the actual program, memory, index and width. No mutation campaign claimed. | E-CLOSE and E-RUN universally quantify shape and fitting metadata states without readiness, positive size, rare-count-zero or successful-read assumptions; E-BOUNDARY/E-RARE make edge and rare domains explicit. | Closed — checked final source; coordinator acceptance pending |
| `INV-PROOF-SEPARATION` | proof-only fields never carry answers or uncharged routing information; | Select controller safety on the canonical allocation | Complete source Safe and actual-run Instruction.Safe/all-prefix Fits at fixed wordWidth, exact value/reads/budget and output bound | ReaderSafety + independent scalar/entry/word leaves + RankSafety + SelectProof -> fixed select source -> Safety.Compiler -> same canonical run | PASS: checked canonical_boundary/empty_shape and symbolic_rare_paths; the expanded run_expectedType fixes the actual program, memory, index and width. No mutation campaign claimed. | E-CLOSE derives Safe for the frozen source, while E-RUN fixes compileAt 0 plus halt 513; shape and semantic stores occur only in proof specifications. The SelectSource SHA256 remains unchanged from the checked value producer. | Closed — checked final source; coordinator acceptance pending |
| `INV-INSTRUCTION-ATOMICITY` | each modeled small step performs the familiar primitive operation it advertises. A constructor whose evaluator body hides recursion, a variable-length scan, repeated rank/select work, decoding, or several arithmetic categories is a macro-step unless that work is expanded into charged transitions or bounded by an explicitly accepted primitive; | Select controller safety on the canonical allocation | Complete source Safe and actual-run Instruction.Safe/all-prefix Fits at fixed wordWidth, exact value/reads/budget and output bound | ReaderSafety + independent scalar/entry/word leaves + RankSafety + SelectProof -> fixed select source -> Safety.Compiler -> same canonical run | PASS: checked canonical_boundary/empty_shape and symbolic_rare_paths; the expanded run_expectedType fixes the actual program, memory, index and width. No mutation campaign claimed. | E-STATIC verifies every compiled primitive field and E-RUN states Instruction.Safe for each actual indexed transition. The identical source contains the fixed eight-copy loop and explicit reader/rank expansion; no macro instruction or callback was added. | Closed — checked final source; coordinator acceptance pending |

## Planned command ledger

| Role / command | Covered paths and rows | Distinct failure mode | Tree / runtime and deadline plan | Outcome |
| --- | --- | --- | --- | --- |
| Development: narrow direct Lean checks of SelectSafety | New source; independent word/entry/scalar leaves, then rank-dependent close wrapper | Numeric inequalities, shift/divisor obligations and invariant composition | Dirty shared tree, explicit single-slot handoff; initially expect 5–20 s based on prior SelectProof 15.48 s. Yield at 10 s, inspect active process before any timeout retry. | PASS; exact final verification ledger below |
| Final required: direct Lean `-o/-i SelectSafety` | All semantic/safety/run rows on the final source hash | Kernel checks final unchanged source and exact consumers | Record exact hash, warmed prerequisites and preceding observed runtime; no overlapping process or broad Lake fallback. | PASS; exact final verification ledger below |
| Final required: separate imported expected-type consumer and axiom inventories | Canonical source, same run, indexed safety, all fuel prefixes, encoded fields and final packet | Reject weakened/sibling propositions through independent exact types; inspect proof dependencies | Import final artifact, approximately 5–10 s from previous imported check. | PASS; exact final verification ledger below |
| Final required: repository trust/native scan and owned diff whitespace checks | Source trust footprint and final documents | Forbidden escapes, unsupported imports and whitespace including untracked files | Final owned hashes; use no-index check for untracked files. | PASS; exact final verification ledger below |
| Conditional / lead-owned: full build/gate, committed-range and strict design-policy checks | Full-query integration and shared ledger | Broad composition and integration policy | Frozen prompt assigns these to lead; no worker commit. | Not a local mandatory run |

No mutation campaign is assigned or claimed. Source safety is not assumed in the
final canonical proposition. The final report can state CANDIDATE_COMPLETE only
after every row above has checked, object-specific evidence.


## Final verification ledger

| Check | Exact outcome |
| --- | --- |
| Project skill preflight at governance 4639223bc8130b0ef752270b5cbdd74325abcd60 | PASS; required rmq-proof-sprint and actual three-skill runtime catalog |
| Final full diagnostic, all declarations at 30,000 heartbeats | PASS, no warnings, 7.5928716s |
| Final SelectSafety source `lean -o ...SelectSafety.olean -i ...SelectSafety.ilean RMQ/Core/WordRAM/Packed/SelectSafety.lean` | PASS, no warnings, 8.6856428s; SHA256 7501caea587ae35362c8edc1308ef5e34ceefcc0b84bbd43a40d89a9bec28155 |
| Separate `.lake/build/SelectSafetyImportedConsumer.lean` full independently spelled run type + 14 axiom inventories | PASS, 12.7440154s; only propext,Classical.choice,Quot.sound |
| Repository forbidden escape/import scan and native-decision scan | Both empty; rg exit 1 means no matches |
| Owned whitespace checks including untracked source/matrix/report | PASS; final report records no-index check results |
| Full build/gate, strict design policy and exact committed-range check | Lead-owned by frozen prompt; no local commit or broad gate |

Development diagnostics exposed register projection normalization and concrete
evaluator unfolding at proof joins. The final repair abstracts the block,
reader, continuation or repeat count in the proof helper before instantiating
the same fixed source. No heartbeat limit was raised and no source instruction,
reader ABI, word width or allocation changed.

# PQ1-SS evidence appendix

The evidence blocks below are part of the evidence cells of this matrix. Each
quotes the complete checked declaration type, not merely a theorem name. `E-RUN`
expands the shared execution-safety predicate so that all static fields, indexed
transitions, fuel prefixes and indexed read backing remain visible. Lean binders
in each declaration are universally quantified.

Common object chain: `shape` fixes `shapeMemory shape`, `metadata shape` and
`wordWidth shape.size`. Canonical ReaderSafety and RankSafety prove the actual
reader and rank blocks safe on that memory. The scalar/entry/word/dense/rare
proofs compose into `selectCloseBlock logicalReadBlock`. `rank_compiled_safety`
consumes that exact source Safe proof through `Block.compile_with_halt_safe`;
`SelectProof.selectCloseRun_canonical` supplies value and ordered receipts for
exactly `run (shapeMemory shape) selectCloseProgram 91243 ⟨regs,0,.running⟩`.
`selectCloseProgram` is the same block's `compileAt 0 ++ [.halt 513]`.


## E-WORD

```lean
theorem selectWordBlock_safe (shape : CartesianShape) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs)
    (hl : s.regs 401 ≤ packedReviewerCellWidth shape.size) :
    (selectWordBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s
```

```lean
theorem selectWordBlock_output_bound (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hl : regs 401 ≤ packedReviewerCellWidth shape.size) :
    ((selectWordBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 403 ≤
      metadataEnvelope shape.size
```

```lean
theorem selectWordBlock_execution_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (length : regs 401 ≤ packedReviewerCellWidth shape.size) :
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((selectWordBlock logicalReadBlock).compileAt 0 ++ [.halt 403])
      17754 ⟨regs, 0, .running⟩
```


## E-CLOSE

```lean
theorem selectCloseBlock_safe (shape : CartesianShape) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    (selectCloseBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s
```

```lean
theorem selectCloseBlock_output_position_bound (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) :
    ((selectCloseBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 513 ≤
      2 * shape.size
```

```lean
theorem selectCloseBlock_output_envelope (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) :
    ((selectCloseBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 513 ≤
      metadataEnvelope shape.size
```


## E-STATIC

```lean
theorem selectWordBlock_fieldsFit (width : Nat) (reader : Block)
    (readerFields : reader.FieldsFit width) (cap : 8280 < 2 ^ width) :
    (selectWordBlock reader).FieldsFit width
```

```lean
theorem selectEntryBlock_fieldsFit (width : Nat) (reader : Block)
    (readerFields : reader.FieldsFit width) (cap : 8280 < 2 ^ width)
    (segment indexReg base : Nat) (hs : segment + 4 ≤ 8280)
    (hi : indexReg ≤ 8280) (hb : base + 11 ≤ 8280) :
    (selectEntryBlock reader segment indexReg base).FieldsFit width
```

```lean
theorem selectCloseBlock_fieldsFit (width : Nat) (reader : Block)
    (readerFields : reader.FieldsFit width) (cap : 8280 < 2 ^ width) :
    (selectCloseBlock reader).FieldsFit width
```

```lean
theorem selectCloseProgram_fieldsFit (n : Nat) :
    ∀ instruction ∈ selectCloseProgram, instruction.Fits (wordWidth n)
```


## E-RUN

```lean
theorem selectCloseRun_safe (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (fit : ∀ r, regs r < 2 ^ wordWidth shape.size) :
    let expected := packedSelectCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 512)
    let actual := selectCloseRun (shapeMemory shape) regs
    actual.result = some (optionNatPacket expected.value) ∧
    actual.final.status = .halted (optionNatPacket expected.value) ∧
    actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
    actual.steps ≤ 91243 ∧
    (∀ r, ¬ SelectWrites r → actual.final.regs r = regs r) ∧ ReadOnlyTrace expected.trace ∧
    optionNatPacket expected.value < 2 ^ wordWidth shape.size ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      selectCloseProgram 91243 ⟨regs, 0, .running⟩
```

```lean
theorem run_expectedType (shape : CartesianShape) (regs : Registers)
    (metadata : ∀ i < 174, regs (16 + i) = ((metadata shape)[i]?).getD 0)
    (fit : ∀ r, regs r < 2 ^ wordWidth shape.size) :
    let expected := packedSelectCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 512)
    let program := (selectCloseBlock logicalReadBlock).compileAt 0 ++ [.halt 513]
    let actual := run (shapeMemory shape) program 91243 ⟨regs, 0, .running⟩
    actual.result = some ((expected.value.map (fun position => position + 1)).getD 0) ∧
    actual.final.status = .halted ((expected.value.map (fun position => position + 1)).getD 0) ∧
    actual.reads = expected.trace.flatMap (fun event => match event with
      | .readWord segment index _ => readerReceipts shape (shapeMemory shape) segment index
      | _ => []) ∧ actual.steps ≤ 91243 ∧
    (∀ r, ¬ ((256 ≤ r ∧ r < 311) ∨ (352 ≤ r ∧ r < 371) ∨ (400 ≤ r ∧ r < 412) ∨
      (513 ≤ r ∧ r < 551) ∨ (560 ≤ r ∧ r < 571) ∨ (590 ≤ r ∧ r < 601) ∨
      (640 ≤ r ∧ r < 660) ∨ (8192 ≤ r ∧ r < 8271)) → actual.final.regs r = regs r) ∧
    (∀ event ∈ expected.trace, event.isReadWord) ∧
    ((expected.value.map (fun position => position + 1)).getD 0) < 2 ^ wordWidth shape.size ∧
    (∀ instruction ∈ program, instruction.Fits (wordWidth shape.size)) ∧
    actual.final.Fits (wordWidth shape.size) ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe (wordWidth shape.size) t.before t.instruction ∧
        t.after.Fits (wordWidth shape.size)) ∧
    (∀ index, index ≤ 91243 →
      (run (shapeMemory shape) program index ⟨regs, 0, .running⟩).final.Fits (wordWidth shape.size)) ∧
    (∀ (index : Nat) (t : Transition) (receipt : Receipt),
      actual.transitions[index]? = some t → t.receipt = some receipt →
      receipt.address < 2 ^ wordWidth shape.size ∧ receipt.reply = (shapeMemory shape)[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ wordWidth shape.size))
```


## E-ALLOCATION

```lean
theorem selectCloseRun_sameAllocation (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (fit : ∀ r, regs r < 2 ^ wordWidth shape.size) :
    (shapeMemory shape).length * wordWidth shape.size ≤
      2 * shape.size + allocationRho shape.size ∧
    wordWidth shape.size ≤ 192 * (Nat.log2 (shape.size + 2) + 1) ∧
    (∀ value ∈ shapeMemory shape, value < 2 ^ wordWidth shape.size) ∧
    (selectCloseRun (shapeMemory shape) regs).result =
      some (optionNatPacket (packedSelectCloseLeaf
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 512)).value) ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      selectCloseProgram 91243 ⟨regs, 0, .running⟩
```


## E-BOUNDARY

```lean
theorem canonical_boundary (shape : CartesianShape) (regs : Registers)
    (metadata : MetadataMatches shape regs) (fit : ∀ r, regs r < 2 ^ wordWidth shape.size)
    (boundary : regs 512 = shape.size) :
    (selectCloseRun (shapeMemory shape) regs).result = some 0 ∧
    (selectCloseRun (shapeMemory shape) regs).reads = [] ∧
    (∀ index, index ≤ 91243 → (run (shapeMemory shape) selectCloseProgram index
      ⟨regs, 0, .running⟩).final.Fits (wordWidth shape.size))
```

```lean
theorem empty_shape (shape : CartesianShape) (regs : Registers)
    (empty : shape.size = 0) (metadata : MetadataMatches shape regs)
    (fit : ∀ r, regs r < 2 ^ wordWidth shape.size) :
    (selectCloseRun (shapeMemory shape) regs).result = some 0 ∧
    (selectCloseRun (shapeMemory shape) regs).reads = [] ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      selectCloseProgram 91243 ⟨regs, 0, .running⟩
```


## E-RARE

```lean
theorem symbolic_rare_paths (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (metadata : MetadataMatches shape regs) (occurrence : regs 512 ≤ metadataEnvelope shape.size)
    (word : regs 562 ≤ metadataEnvelope shape.size) (offset : regs 564 ≤ metadataEnvelope shape.size)
    (base : regs 520 ≤ 3 * (metadataEnvelope shape.size * metadataEnvelope shape.size)) :
    (selectLongBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ ∧
    (selectSparseBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩
```
