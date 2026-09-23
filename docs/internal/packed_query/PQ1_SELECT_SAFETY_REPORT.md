Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

# PQ1-SS — canonical select controller word safety

Worker: `metadata_width` / PQ1-SS. Branch: `codex/fully-charged-packed-query-v1`.
Worktree: `C:/Users/poin/.codex/worktrees/a84a/RMQ`.
Assigned base and current HEAD: `067b6ffd350aee08f1496335ce957895f0da3fcc`.
Governance: `4639223bc8130b0ef752270b5cbdd74325abcd60`.
No staging, commit, push, branch/worktree change or shared-ledger edit was made.

The [completed frozen matrix](PQ1_SELECT_SAFETY_MATRIX.md) closes all 13 assigned
and inherited rows. Its E-WORD, E-CLOSE, E-STATIC, E-RUN, E-ALLOCATION,
E-BOUNDARY and E-RARE blocks quote full checked declaration types, including the
expanded expected-type run consumer. The verbatim requirement text and IDs were
preserved. Coordinator acceptance and full-query integration remain separate.

## Result and exact public boundary

`RMQ/Core/WordRAM/Packed/SelectSafety.lean` proves:

```lean
∀ (shape : CartesianShape) (s : Data),
  s.Fits (wordWidth shape.size) → MetadataMatches shape s.regs →
  (selectCloseBlock logicalReadBlock).Safe (shapeMemory shape)
    (wordWidth shape.size) s
```

This covers every fitting occurrence; therefore it also covers the requested
`occurrence ≤ shape.size` domain without an additional precondition. The fixed
word helper needs only fitting Data, canonical metadata and
`length401 ≤ packedReviewerCellWidth shape.size`. Its source result403 is at most
`metadataEnvelope shape.size`, and its compiled appended-halt execution is safe
through every fuel prefix bounded by 17,754.

The canonical close packet513 satisfies both of the following, without a Fits,
readiness, successful-read or occurrence-bound hypothesis:

```lean
∀ (shape : CartesianShape) (regs : Registers), MetadataMatches shape regs →
  ((selectCloseBlock logicalReadBlock).eval (shapeMemory shape)
    ⟨regs, .running⟩).final.regs 513 ≤ 2 * shape.size

∀ (shape : CartesianShape) (regs : Registers), MetadataMatches shape regs →
  ((selectCloseBlock logicalReadBlock).eval (shapeMemory shape)
    ⟨regs, .running⟩).final.regs 513 ≤ metadataEnvelope shape.size
```

The source interfaces are `selectCloseBlock_safe`,
`selectCloseBlock_output_position_bound`, `selectCloseBlock_output_envelope`
and `selectCloseBlock_fieldsFit`. The last theorem covers every encoded source
field for arbitrary reader blocks whose fields fit, when 8,280 is below capacity;
its canonical consumer discharges those premises with the actual reader and the
fixed width. `selectCloseProgram_fieldsFit` includes all compiled jump/branch
PCs and halt 513, including dormant code.

`selectCloseRun_safe` concerns exactly
`run (shapeMemory shape) selectCloseProgram 91243 ⟨regs,0,.running⟩`. It combines
its canonical packet result, halted status, ordered physical receipts, step
bound 91,243, register frame, read-only reference trace, packet word bound and
`RankExecutionSafety` for that same run. The matrix's E-RUN expands this shared
predicate into all encoded instructions, final State.Fits, every indexed
Instruction.Safe transition and fitting after-state, every fuel prefix, and
positionally backed read addresses/replies. It does not replace actual
occurrences with event-value membership.

## Object composition and assumptions

The exact chain is:

1. `shape` fixes `metadata shape`, the counted `shapeMemory shape`, and
   `wordWidth shape.size = 32 + 8 * packedReviewerCellWidth shape.size`.
2. `logicalReadBlock_safe` supplies the actual reader's source safety on that
   memory. Its checked value/frame theorem and output bounds provide the
   decoded packets and lengths used by select arithmetic.
3. The four-entry read/decode proofs, scalar address/finish proofs and the
   eight-copy word invariant compose with canonical RankSafety word/long/sparse
   wrappers. RankProof and SelectProof frame/value results preserve the caller
   registers and relate actual replies to the established select semantics.
4. The dense first/second-word routes and all long/sparse, local/super, missing
   and rejected paths join in `selectCloseBlock_safe`. No source Safe certificate
   remains as a hypothesis of that canonical theorem.
5. `rank_compiled_safety` applies `Block.compile_with_halt_safe` to this exact
   block. Its actual program is `compileAt 0 ++ [.halt 513]`, and its budget is
   exactly 91,243. `selectCloseRun_canonical` supplies semantic result and receipt
   equality on the identical program, memory, fuel and initial state.
6. `selectCloseRun_sameAllocation` combines that run with
   `shapeMemory.length * wordWidth ≤ 2*size + allocationRho`, fitting stored
   words, and `wordWidth ≤ 192*(Nat.log2(size+2)+1)`.

The live machine assumptions are the declared fitting register/status predicate
and canonical MetadataMatches. Metadata setup is a previously checked charged
producer, discharged by the full-query caller; this local boundary neither
assumes nor hides a successful payload reply. Shape and semantic read stores
occur in proof specifications, while the fixed primitive source reads its
runtime geometry from the charged register bank. Natural-number arithmetic,
word/address capacity, guarded subtraction, shift counts and static encodings
are all accounted at the same declared width. The result concerns the explicit
word-RAM transition model, not measured Lean runtime performance.

## Verification and anti-vacuity evidence

- Project skill preflight: PASS at the governing commit, required
  rmq-proof-sprint with the actual runtime catalog. The canonical completion
  gate was applied, and the matrix was frozen before implementation.
- Final complete diagnostic at 30,000 heartbeats: PASS, no warnings, 7.5928716s.
- Final actual source `.olean/.ilean`: PASS, no warnings, 8.6856428s.
- Separate imported independently spelled run consumer: PASS, 12.7440154s. The
  durable `SelectSafetyConsumers.run_expectedType` also fixes the complete
  expanded proposition in the source artifact. It would fail to type-check
  against a weakened value, width, program, memory, indexed safety or prefix
  conclusion. No mutation campaign is claimed.
- Fourteen theorem dependency inventories: only `propext`, `Classical.choice`
  and `Quot.sound`. Inventories include word/source/rare/dense safety, exact
  position and envelope bounds, static fields, compiled execution, same-run
  semantics and same-allocation composition.
- Both repository scans required by AGENTS.md returned no matches: forbidden
  trust escapes/import Mathlib, and native_decide/Lean.ofReduceBool.
- `canonical_boundary` checks occurrence=size: result 0, no payload reads and
  fitting prefixes. `empty_shape` universally checks all fitting requests on
  size 0. `symbolic_rare_paths` checks both exception branches without restricting
  longCount or sparseCount to 0. Missing replies are allowed throughout the
  source safety and value proofs; four entry reads happen before presence tests.
- Owned whitespace checks, including no-index checks for untracked files, pass.
  Git's LF-to-CRLF advisory is not a whitespace error.

Only one Lean process ran at a time, with explicit handoffs. Development
failures were resolved by typed register projection normalization and generic
proof composition before fixed-reader/repeat instantiation. The final source
contains no added heartbeat option. Broad builds/gates, exact committed-range
checks and strict design-policy integration checks are lead-owned by the frozen
prompt; they were not substituted for these narrow checks or redundantly run.

## Exact source identities

| File | SHA256 |
| --- | --- |
| SelectSafety.lean — final checked owned source | `7501caea587ae35362c8edc1308ef5e34ceefcc0b84bbd43a40d89a9bec28155` |
| SelectSource.lean — unchanged during PQ1-SS | `e0f6ea4655d3241ea067fb0c3361f879688906f367fc2e9e87b008589ce59a07` |
| SelectProof.lean — unchanged checked value/receipt producer | `c81b09fc5f6d7a373b5ef0a51a89feac57d1637a3cc995a9c083f32c336bcecb` |
| RankSafety.lean — consumed canonical safety producer | `96be9dd9816325bd5f5648703677937d5662bf464c7bf2576cd318ca0e451121` |
| ReaderSafety.lean — consumed actual reader safety producer | `d9c17e4c48f95df2ca3ff95c18de82c5f8f535328f8916b14f12f35d6a8716ec` |

Owned deliverables are SelectSafety.lean, this report and its matrix. The select
source program, ISA, width, allocation, decoder ABI and prior value theorem
were preserved. No public headline was changed by this leaf; the lead owns the
combined milestone's public inventory and claim synchronization.

## Proof digestion and proposed design rationale

Conceptually, the former exact-value select execution now carries word bounds
through every primitive action. A bounded eight-copy invariant covers the word
loop. Canonical decoded metadata and reply bounds cover dense and exception
arithmetic, and the compiler carries source safety into the actual transition
sequence. The tighter selected-position bound comes from the already checked
canonical select semantics and is exported for the next controller stage.

In plain English, this is the same program returning the same answer through
the same reads, now proved unable to overflow its declared modeled word or use
an out-of-width shift/address/encoded operand along the run. All dormant
instruction fields also fit. The semantic shape assumptions and initial
metadata/register boundary remain explicit.

Proposed design-ledger append for the lead: use the existing source Safe and
compiled safety calculus for select, with `E=64*(2^oldWidth)^2` as a conservative
intermediate arithmetic envelope and `packet≤2n` as the canonical handoff bound.
Keep raw tagged packets separate from decoded arithmetic bounds. Generalize
reader blocks, continuations and repeat counts in proof helpers before
instantiating the fixed program; direct reduction of the concrete reader copies
caused kernel normalization failures without adding semantic content. Rejected
alternatives were a larger machine word, a supplied final Safe premise, excluded
rare/missing paths and evaluator macro steps. Consequences: unchanged executable
code and allocation, reusable source/compiled interfaces, and an explicit
bound needed by LCA arithmetic. No ADD/process change was made.

A skeptical graduate student should next ask whether the complete charged
setup/select/LCA/final-rank query discharges these initial metadata/register
premises and preserves the same allocation and indexed safety throughout. This
is the named downstream query join, not an unproved local select obligation.
All assigned and inherited PQ1-SS acceptance criteria have checked evidence in
the matrix; no local criterion is deferred.
