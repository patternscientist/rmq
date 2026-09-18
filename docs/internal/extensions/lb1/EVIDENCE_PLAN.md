# LB-1 exact evidence map

This file expands the frozen matrix without changing its rows. Generic and
validation source elaboration is recorded in COUNT_PROOF_NOTES.md; the adapter's
successful elaboration is recorded in PACKED_PROOF_NOTES.md. The propositions
below are checked. Final local runtime/replay evidence is in FINAL_DISPOSITION.md; coordinator broad certification remains outstanding;
no entry here records coordinator acceptance.

## Count and actual allocation

REQ-LB-COUNT uses the single record
`ExactRMQBoundedEncoding n B`: its encoder accepts every ordinary List Int,
its decoder accepts only bits and endpoints, its payload length is bounded for
every xs with xs.length=n, and its exactness field covers every left,len with
0<len and left+len<=n. The proved universe has Nodup, length 2^(B+1)-1 and
membership iff bit length<=B. Equal codes give SameRMQBehavior, hence equal
shapes. Encoding the canonical representatives injects shapesOfSize n into
that universe. The checked generic conclusion is
`shapeCount n <= 2^(B+1)-1`, followed by
`doubledLogSlackLower n <= 2*(B+1)`.

REQ-LB-PQ1 consumes these literal adapter propositions:

- For all width>0 and every finite words list whose entries are below 2^width:
  `deserializeWords width (serializeWords width words) = words`.
  Equality of serialized lists therefore implies equality of those word lists.
- For every ordinary xs:
  `(allocationBits xs).length = (buildMemory xs).length * wordWidth xs.length`.
- `reconstructedMemory xs = buildMemory xs`, where the left side is literally
  `deserializeWords (wordWidth xs.length) (allocationBits xs)`.
- For all xs,left,right:
  `allocationDecoder xs.length (allocationBits xs) left right =
    if ValidRange xs left right then some (scanWindow xs left (right-left)) else none`.
  A successful returned index satisfies LeftmostArgMin on those same arguments.
- Equal Cartesian shapes imply equal buildMemory and equal allocationBits;
  equal allocationBits on representatives of two size-n shapes imply those
  shapes are equal. No value-list injection is asserted.

REQ-LB-MODEL fixes
`UniformAllocationBudget n B :=
  forall xs : List Int, xs.length=n ->
    (buildMemory xs).length * wordWidth n <= B`.
The exact generic instance is `allocationEncoding n B budget`, with
encode=allocationBits and query=allocationDecoder n. Thus any such B satisfies
the finite count and doubled lower inequalities. At
`B=2*n+allocationRho n`, canonicalAllocationBudget supplies the hypothesis.
The actual per-input upper bound is
`(allocationBits xs).length <= 2*xs.length+allocationRho xs.length`,
with `LittleOLinear allocationRho`. The lower side quantifies a uniform budget;
it is not an assertion about each individual allocation. Complete code/scratch
capacity separately uses queryCompleteRho and literal program/register counts.

REQ-LB-CONSUMER uses publicContract, composedConsumer and checkO01..checkO16.
Each expected type is literal in the validation file; proofs consume the named
packedAllocationOptimality_holds. canonicalEncodingConsumer also fixes the
actual generic instance's encode/query fields and applies the independently
typed genericLowerConsumer to that instance. The lower bound therefore has an
object chain through the actual allocation, not just a similar numeric cap.
pinAllocationDecoder fixes `fun n bits left right =>
  queryNat (deserializeWords (wordWidth n) bits) n left right`.
No xs, shape or proof is supplied to this decoder; its only captured input is n.

## Inherited semantic/model rows

INV-STORE-IDENTITY and INV-PUBLIC-COMPOSITION: checkO03/checkO04/checkO15 pin
serialized length, full memory equality and equality of every fuel-prefix run.
For all xs,left,right,fuel, the run on reconstructedMemory equals the run on
buildMemory, with identical queryProgram and initialState xs.length left right.
Every checkM01..checkM33 subsequently concerns reconstructedMemory. The O04/O15
sibling and deletion attacks test these exact equalities; comparing sizes alone
would not satisfy them.

INV-VALUE-DEPENDENCY and INV-PROOF-SEPARATION: allocationDecoder's literal body
calls queryNat on decoded numeric words. queryNat uses the fixed primitive
program and its halted result packet. No reference scan is an executable input
to that program. The exact scanWindow formula is a proved semantic conclusion.
The source load operation reads memory into the actual destination register;
run derives the final status from those operations. Null and constant-answer
decoder mutations must fail allocationDecoder_exact's original value equation.
Pure counting has no charged reads; mathematical deserialization is outside
the charged primitive profile.

INV-SEMANTIC-NONVACUITY and INV-ALL-SIZE: exact decoding quantifies every xs,
including empty and singleton lists, without readiness or compatibility
premises. Positive windows have the same ValidRange guard throughout.
For every n, List.replicate n 0 witnesses a size-n input; the canonical encoding
exists for every n. Empty input has one shape and no positive valid window.
The empty-only decoder field mutation must fail the universal checkO05.
Generic null/wrong/advice controls use query_exact with its original quantifiers.

INV-TRACE-EXECUTION and INV-NO-SYNTHETIC: checkM27 pins each transition occurrence
by index, its prefix run's state, the actual producing load instruction, and
execute on reconstructedMemory. checkM28 relates the same run's ordered reads
to the reference expansion with that reconstructed memory. List.Mem is not
substituted for an occurrence-specific claim. No new trace constructor or replay
execution is introduced by this extension.

INV-STORE-AGREEMENT: checkM30 states, for all xs,memory,left,right, agreement at
every receipt address of the actual reconstructed-memory run implies equality
of the entire run (therefore result, cost and trace). The premise and both runs
use the same program, queryBudget and initialState. The dynamic receipt
condition is inherited from the accepted execution-derived agreement proof.

INV-READ-BACKING: checkM27 fixes each load receipt's address from the producing
pre-state register and its reply to
`(reconstructedMemory xs)[receipt.address]?`. checkM26 combines this with
address/reply word bounds under the original endpoint guards. checkM32 rules
out failed canonical loads. Deleting the positionalReadBacking field must fail
checkM27 after the modified producer itself compiles.

INV-WORD-WIDTH, INV-ADDRESS-WIDTH and INV-WIDTH-SCALING: checkM03 pins the single
n-only width between log2(n+2)+1 and 192*(log2(n+2)+1).
checkM06 bounds every reconstructed word below 2^wordWidth; checkM07 covers
every allocation address <=memory.length, including the end sentinel.
checkM08 checks every encoded instruction, including dormant code and operands.
checkM23..checkM26 retain representable endpoint premises while covering final
state, every executed transition, every fuel prefix and every load. The total
natural-number wrapper does not remove those raw-machine safety premises.

INV-INSTRUCTION-ATOMICITY: all transported fields concern the unchanged fixed
PQ1 program over its accepted load, register, arithmetic, comparison and control
instructions. The bit-list decoder and outer encodeInputs/packet conversion
receive no charged primitive-time claim. The new extension cannot reclassify a
whole-list conversion as one primitive step.

INV-PROGRAM-ACCOUNTING and INV-GLOBAL-PHYSICAL-MACHINE: checkM05 counts the
literal reconstructed allocation plus flattened queryProgram instruction
encodings plus queryRegisterCount+3 words at the same wordWidth.
checkM11..checkM14 pin program bound, register/scratch counts and the theorem
that all registers outside the finite bank remain zero at every prefix.
Shape-dependent metadata stays in buildMemory and survives whole-list recovery.
All primitive segments therefore share the same pre-execution numeric store;
no suffix-only embedding is used.

INV-ORACLE-INDEPENDENCE and INV-VALIDATION-REACH: runtime cases construct actual
allocationBits, recover memory and execute allocationDecoder. Empty/singleton/
tie answers are independent literal expectations, with scanWindow checked
separately where informative. Zero-word fixtures cover the serializer and
decoder directly. Different-valued same-shape inputs intentionally share bits.
The runtime registry does not test a predecessor decoder or use its own result
as the expected answer.

INV-CATEGORY-SEPARATION: bits, numeric memory, proof records, primitive steps,
literal code, finite scratch and measured build/runtime durations are reported
separately. checkM21/22 refer to steps and category partition of the same run;
no statement identifies Lean evaluation duration with the model's query bound.

INV-CERTIFICATE-ANTI-BYPASS: 49 independent literal consumers project all 16
optimality and 33 transported machine fields. Replay O/M cases weaken the
field proposition and its initializer to True, require the producer to pass,
then require a diagnostic in that exact consumer declaration. Additional
deletions, sibling memory/run/budget substitutions, and empty-only exactness
exercise different bypass classes. The named public proposition and generic
lower proposition are also mutated, each with its independent consumer.

INV-MUTATION-REPRODUCIBILITY, CHK-LB-CONTROLS and the three REPLAY rows:
REPLAY_REGISTRY.json version 3 pins 63 proof/control cases and six runtime cases.
scripts/variable_payload_replay.ps1 independently fixes the exact same ordered
case list. It freshly compiles the generic and packed producers before checking
actual structure metadata, then freshly compiles the validation client. Backups
capture these checked baseline artifacts, so source cleanliness is not used as
a proxy for cache freshness. Missing, duplicate or unselected cases fail; omitted, valid, empty,
whitespace, malformed and unknown selector behavior is explicit. Runtime
startup and one known selector precede the full campaign. Every child is owned
and bounded; exit/stderr are retained and resource failures are inconclusive.
Each source mutation and overwritten olean restores exact bytes in finally;
restoration and clean worktree/index/untracked state are checked after every
case and at exit. A02 adds a harmless proof-only wrapper containing the unchanged
public certificate and an unused True note, then requires producer, inventory
and typed consumer acceptance. Positive unchanged, advice, and zero-width
excluded-domain controls also prevent a rejection-only story. Full outcomes remain
pending, and source review is not a semantic verdict.

## Development verification evidence (historical)

- Generic 15-module source check: exit 0, new leaf 18.991 seconds, 600-second
  deadline; evidence/build-20260912T071953550.jsonl.
- Version 1 registry/local selector controls: 56 expected cases, six runtime
  identifiers; discovery only. Version 2 adds six deletion/sibling/domain cases.
- Version 2 registry/local selector controls: PASS, 62 expected cases and six
  runtime identifiers; source/semantic replay still pending.
- Actual six subprocess selector boundaries passed on the earlier registry
  version; the version change requires updated final evidence.
- Version 3 registry/local selectors and both diagnostic-boundary cases passed.
  Its six actual subprocess selector boundaries also passed, including omitted
  selection of all 63 cases; evidence/selector-controls-v3.json preserves exits,
  stdout/stderr, duration and ownership. This is process evidence, not a semantic
  mutation verdict. The zero-serializer case now pins serializeWords_length,
  the first exact equation falsified; later proofs may inherit an elaboration
  error placeholder and cannot be used as an assumed diagnostic surface.
- Owned Windows descendant deadline: the initial ten-second startup attempt was
  inconclusive; the thirty-second probe passed and found the descendant absent
  after job cleanup. POSIX execution is uncovered. See
  evidence/process-controls-development.json.
- Independent route/replay source reviews are process evidence. They do not
  certify unelaborated adapter declarations or unexecuted mutation cases.
- The clean adapter and independent validation source checks now pass. All 49
  field projections, composedConsumer, data-path pins and kernel boundary
  propositions are elaborated; separate generic consumer checks also pass.
- The exact 4/16/33 metadata inventories, two accepted fixtures and eleven
  rejected predicate calls pass after correcting the parent fixture's syntax.
- All 20 named axiom records are present and use only propext,
  Classical.choice and Quot.sound. Both full RMQ trust-token scans have no hits.
  See evidence/axiom-summary.json and the preserved full diagnostic output.

## Final exact-source evidence, 2026-09-12

Implementation 5033ce54 has all local replay/focused/runtime/trust outcomes recorded in FINAL_DISPOSITION.md and evidence/final-evidence-manifest.json. The frozen29 rows remain unchanged. Earlier pending statements describe development versions; the final disposition is authoritative for local outcomes. Coordinator full build/gate and acceptance remain outstanding.
