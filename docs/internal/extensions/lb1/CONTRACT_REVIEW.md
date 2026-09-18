Status: INCOMPLETE
Phase: independent contract/route review; implementation and final audit remain open.

# LB-1 independent contract and route review

Auditor: `/root/contract_review`.
Base, source HEAD, and workflow governance:
`0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Branch: `codex/lb-1-variable-payload`.
Worktree: `C:/Users/poin/.codex/worktrees/2270/RMQ`.
Frozen contract: `FROZEN_REQUIREMENTS.md`, `FROZEN_INVARIANTS.md`,
`ACCEPTANCE_MATRIX.md`, and `CONTRACT.md` in this directory.
Scope: read-only review of the pinned generic interface, proposed serializer,
decoder and capstone route, and existing source supporting that route. This is
neither an implementation completion report nor an exact-commit acceptance audit.
The only auditor-owned write is this report. Parent and adapter workers own all
implementation and acceptance-matrix edits.

## Verdict and evidence level

The proposed route is feasible. No blocking mathematical defect was found in the
frozen interface. The conclusions below are source inspection and contract-review
evidence. Existing theorem types and definition bodies were inspected, but no
Lean builds or executable mutation checks were run by this auditor. New LB-1
theorems, controls and their final consumer remain implementation obligations.

Project-skill preflight passed at the exact governance and HEAD above, with all
three canonical RMQ skills present in the checkout and runtime catalog, and
`rmq-proof-sprint` explicitly required. The canonical skill, completion gate,
relevant known failure modes, and `docs/internal/AUDIT_PROTOCOL.md` were read.

## Required implementation obligations

1. **Transport machine facts to the reconstructed memory explicitly.** Existing
   `FullyChargedPackedQueryCapstone` fields in
   `RMQ/Core/WordRAM/Packed/Capstone.lean` hardcode `buildMemory xs`; carrying that
   certificate beside serialization alone does not establish composition. Prove
   `deserializeWords (wordWidth xs.length) (serializeWords (wordWidth xs.length)
   (buildMemory xs)) = buildMemory xs`, then use it in the checked consumer's exact
   allocation, run, safety, backing, and agreement propositions. Equality of the
   entire memory also preserves failed reads and allocation length.

2. **Preserve the machine's endpoint domain.** `queryNat_exact` in
   `RMQ/Core/WordRAM/Packed/QueryCorrect.lean` is total over natural endpoints, but
   `queryRun_execution_safe` in `RMQ/Core/WordRAM/Packed/QuerySafety.lean` requires
   both endpoints below `2 ^ wordWidth xs.length`. Valid ranges imply those
   bounds. Invalid representable ranges may use the existing guard/safety facts;
   arbitrary invalid natural endpoints must not acquire unconditional raw-machine
   safety through the total wrapper.

3. **State both uncharged boundaries.** Serialization/deserialization has no
   charged time theorem. Additionally, `QuerySource.lean` explicitly excludes the
   outer `encodeInputs` check from primitive cost; packet decoding also sits
   outside `queryProgram`. The inherited instruction bound describes the unchanged
   primitive run after reconstruction.

4. **Test advice uniformity semantically.** The fixed decoder field and
   universally quantified exactness provide the needed information-theoretic
   uniformity. A Lean function type alone does not prohibit a closure from
   syntactically capturing an `xs` or shape. Inspect the actual canonical decoder
   definition, and make the negative control fail universal exactness or an
   independently pinned interface, not a binder-name check. A decoder chosen
   separately for each input without a proof that it answers every size-n input
   does not satisfy the frozen encoding interface.

These are obligations of the feasible implementation route, not claims that an
already implemented candidate failed. They do not narrow the frozen requirements.
The parent has consumed these obligations; its adapter assignment explicitly
requires transport of the machine fields.

## Frozen requirement reconstruction

- **REQ-LB-COUNT:** The proposed enumerator over lengths `0..B` gives the appropriate
  capacity `2^(B+1)-1`. Equal encoded representatives imply equal valid-window
  answers; `Cartesian.shape_eq_of_sameRMQBehavior` then recovers shape equality.
  `SameRMQBehavior` in `RMQ/Core/Shape.lean` requires equal lengths and equal
  `scanWindow` answers on every nonempty in-bounds half-open window. Representative
  length and shape recovery supply the finite-domain bridges. Applying
  `LowerBound.two_mul_bits_lower_of_cubic_square_bound` at `bits = B+1` to
  `EncodingLowerBound.shapeCount_cubic_square_lower` gives precisely
  `doubledLogSlackLower n <= 2*(B+1)`. No fixed-length encoding conversion is needed.
  The lower expression expands to `4*n - (3*Nat.log2 (2*n+1)+3)`.

- **REQ-LB-PQ1:** `Allocation.buildMemory` depends only on the Cartesian shape.
  `buildMemory_words_fit`, positive `wordWidth`, `uniform_flatten_slice`, and
  `bitsToNatLE_natToBitsLE_of_lt` support the proposed serialization inverse.
  Exact serialized length must remain `buildMemory.length * wordWidth`, including
  zero cells and final allocation padding. Deserialization must receive only n,
  serialized cells and endpoints; original input and shape occur in correctness
  proofs, not executable arguments. Same-shape value lists intentionally share
  memory. The inverse is required on every finite word list satisfying the word
  bound, not only canonical allocations.

- **REQ-LB-MODEL:** Use `forall xs, xs.length = n -> allocationBits xs <= B` as the
  uniform-budget hypothesis. Combine its induced bounded encoding with the
  existing actual-allocation upper bound and `allocationRho_littleO`. The upper
  expression bounds allocation; it is not an equality for every input. Preserve
  `queryCompleteRho` separately when including fixed program and scratch. Length
  observation is part of the declared variable-payload model; no padding to B or
  assumed equivalence with the existing fixed-length encoding is justified.

- **REQ-LB-CONSUMER:** One exact-type consumer must visibly consume the generic
  instance, exact decoder, serialization inverse, shape injection, budget lower
  bound, and actual upper bound. Machine claims require the transported facts
  described above. A conjunction containing an unrelated predecessor certificate
  does not by itself establish identity of the executed and serialized objects.

- **CHK-LB-CONTROLS:** Empty and singleton domains are intentional boundary cases.
  Null decoding fails singleton exactness. Constant empty payload with one decoder
  cannot serve both `[0,1]` and `[1,0]` on `[0,2)`. At `n=2`, the coarse doubled-log
  lower expression is zero, so these negative controls must target exactness or
  exact finite capacity, not that weaker numerical corollary. Zero payload at
  `n=1` is a useful permitted n-only-advice control because there is one Cartesian
  shape. Equal-key expected answers must use the independent leftmost reference.
  Empty bitstrings versus one and multiple zero words must preserve lengths.
  Deleted/weak exactness and public fields must break the independently pinned
  positive proposition. Advice-oracle mutations must violate that same uniform
  decoder/exactness contract.

- **REPLAY-EXACT-REGISTRY:** A nonempty exact versioned case inventory and
  executed/expected accounting remain implementation obligations. This review
  produced no replay evidence.

- **REPLAY-SELECTOR-NONVACUITY:** Omitted, valid, empty, whitespace, malformed and
  unknown selector behavior remains to be pinned and tested at the command
  boundary. No focused success may select zero cases.

- **REPLAY-SUBPROCESS-DEADLINE:** Owned bounded subprocesses, exit/stderr
  preservation, finally restoration and exact byte verification remain required.
  A host condition that was not exercised remains uncovered.

## Frozen inherited invariant applicability

- **INV-STORE-IDENTITY:** Full reconstruction equality transfers the exact counted
  list, including its length; require that equality at the consumer.
- **INV-VALUE-DEPENDENCY:** `Primitive.execute` loads actual numeric memory into
  registers. `run` folds those transitions and `Run.result` projects the final
  halted state. The new decoder must call that run through `queryNat` using its
  reconstructed memory, without a separately supplied answer.
- **INV-SEMANTIC-NONVACUITY:** Universal exactness over every size-n input and every
  valid nonempty window supplies the correct domain; shape recovery uses the
  expanded operational reference semantics. Null/wrong-answer controls must
  challenge this exact proposition.
- **INV-TRACE-EXECUTION:** `run` derives transitions recursively and `Run.reads`
  filters their receipts. Transport the actual run, not a reconstructed trace.
- **INV-STORE-AGREEMENT:** `queryRun_agreement` preserves the complete run when a
  supplied memory agrees at its ordered execution's read addresses. Transport
  both the canonical run and the memory lookup premise to the decoded list.
- **INV-READ-BACKING:** `queryRun_read_at` retains occurrence index, actual prefix
  pre-state, producing instruction, execution equation, address and memory reply.
  Transfer these exact arguments through the memory equality.
- **INV-WORD-WIDTH:** `buildMemory_words_fit` covers the canonical cells; runtime
  safety bounds returned packet/state values. Both use the declared n-only width.
- **INV-ADDRESS-WIDTH:** Allocation sentinel fit, `programFieldsFit`, transition
  safety and read-width fields cover their distinct obligations. The instruction
  encoding enumerates all numeric operands, including dormant instructions.
- **INV-INSTRUCTION-ATOMICITY:** The unchanged primitive evaluator uses the
  declared arithmetic/Boolean/transfer/load operations. Deserialization must
  remain outside its charged transitions. No new macro-step follows from the
  mathematical bit decoder.
- **INV-PROGRAM-ACCOUNTING:** `queryProgram` is a closed constant; `initialState`
  contains only n and endpoints. Shape-dependent counts and descriptors reside
  in counted `metadata`. `Accounting.lean` charges the actual instruction encoding
  and finite register bank separately from data payload.
- **INV-ORACLE-INDEPENDENCE:** New fixture expectations must come from independent
  `scanWindow`/leftmost semantics, not from the serialized decoder result.
- **INV-VALIDATION-REACH:** New controls must import and execute the serialized
  decoder; predecessor query validation alone is insufficient.
- **INV-ALL-SIZE:** Exactness remains universal over all assigned n and inputs.
  Empty-input valid-window exactness is intentionally vacuous with one Cartesian
  shape; singleton and invalid-range controls expose the relevant boundaries.
- **INV-PROOF-SEPARATION:** Original inputs and Cartesian shapes may occur in
  proof statements and preprocessing. The decoder's executable definition must
  retain only n, payload and endpoints, plus any genuinely fixed n-only advice.
- **INV-NO-SYNTHETIC:** Whole-run transport preserves actual transitions and
  receipts. It must not be replaced by a trace replay accompanying an answer
  computed elsewhere.
- **INV-CATEGORY-SEPARATION:** Keep payload capacity, fixed code, finite scratch,
  external size/advice, mathematical decoding, primitive cost and Lean execution
  behavior separately identified.
- **INV-PUBLIC-COMPOSITION:** Consumer fields must mention the same serialized
  allocation, reconstructed memory, width, initial state and run, preserving the
  validity and representability domains of their source facts.
- **INV-CERTIFICATE-ANTI-BYPASS:** Required exact-type consumers must project every
  mandatory new certificate field at its exact proposition and object arguments.
- **INV-MUTATION-REPRODUCIBILITY:** Committed replay and independently pinned
  consumer types remain necessary; this source review did not run mutations.
- **INV-GLOBAL-PHYSICAL-MACHINE:** Full list reconstruction provides one
  pre-execution memory for every query segment, including failed accesses. The
  unchanged program uses physical numeric loads; serialization does not establish
  an additional bit-addressed query-machine implementation.
- **INV-WIDTH-SCALING:** Transport memory fit, sentinel fit, exhaustive program
  field fit and `RankExecutionSafety`, retaining endpoint premises. Use the same
  n-only `wordWidth` with the existing logarithmic lower and upper bounds.

## Rejected objections and next target

Observed variable payload length is explicitly permitted, so no separate length
delimiter is required for this model. Width is positive and fixed per n; exact
bitstring length distinguishes different counts of zero words. Distinct value
lists sharing a shape do not challenge the requested shape injectivity. The
existing machine can be reused without changing its algorithm once the complete
numeric memory is recovered. None of these observations supplies the new
serialization, uniform encoding or capstone proof automatically.

The next target is the complete adapter and checked consumer with the exact
transport and domain obligations above, followed by the persisted controls and
final exact-commit audit. No requirement is deferred or narrowed by this report.

## Commands and verification disposition

- Project skill preflight passed with exact governance above and actual runtime
  catalog `rmq-coordinator,rmq-proof-sprint,rmq-audit-prompt`.
- Read-only source and frozen-contract inspection supplied the review evidence.
- The required trust scan over `RMQ` and `lakefile.toml` found no forbidden tokens.
- The `native_decide|Lean.ofReduceBool` scan over `RMQ` found no matches.
- Working-tree `git diff --check` passed before persistence. Git reported only
  informational line-ending conversion warnings on parent-owned decision logs.
- No Lean/Lake builds, runtime replay, mutations, broad gates, integration or
  commits were performed. Those checks would not certify a route proposal and
  remain owned by the implementation/final-verification phase.
- Post-persistence strict claim drift, strict design checking with the exact base,
  and report whitespace checks are recorded in the accompanying task output.
  A shared-tree design result is phase evidence, not exact-commit certification.
