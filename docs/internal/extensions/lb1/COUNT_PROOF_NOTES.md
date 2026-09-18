# LB-1 generic counting proof leaf

Status: generic counting leaf implemented and elaborated; parent-owned packed
join, replay, trust inventory, final hygiene and independent acceptance remain.

Owned source: `RMQ/Core/EncodingVariableLowerBound.lean`.
Base/governance: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Worktree: `C:/Users/poin/.codex/worktrees/2270/RMQ`.
The contract in `CONTRACT.md` and acceptance matrix were frozen before this
source was written. The leaf does not modify shared modules or public aliases.

## Exact interface and composition

`RMQ.ExactRMQBoundedEncoding (n B : Nat)` has executable fields
`encode : List Int -> List Bool` and
`query : List Bool -> Nat -> Nat -> Option Nat`. Its proof fields are exactly
the frozen uniform bound and valid-window contract:

```lean
length_le : forall xs, xs.length = n -> (encode xs).length <= B
query_exact : forall xs, xs.length = n ->
  forall left len, 0 < len -> left + len <= n ->
    query (encode xs) left (left + len) = some (RMQ.scanWindow xs left len)
```

The source chain is:

1. `sameRMQBehavior_of_encode_eq`: equal payloads on two size-n lists force
   equal `scanWindow` answers for every valid nonempty half-open window.
2. `shape_eq_of_encode_eq` consumes
   `Cartesian.shape_eq_of_sameRMQBehavior` on precisely those lists.
3. `shapeEncode E shape := E.encode shape.representative` uses computed
   canonical representatives. Their length and shape come from existing
   `representative_length`, `ShapeOfSize.size_eq`, and `shape_representative`.
4. `shapeEncode_injective_on` proves injectivity only on
   `Cartesian.shapesOfSize n`. No value-list injectivity or generic equality
   of encodings for same-shape inputs is assumed or asserted.
5. `shapeCount_le E : Cartesian.shapeCount n <= 2^(B+1)-1` applies the existing
   finite injection theorem to that source list and the actual bounded universe.
6. `doubledLogSlackLower_le E :
   EncodingLowerBound.doubledLogSlackLower n <= 2*(B+1)` weakens capacity to
   `shapeCount n <= 2^(B+1)` and consumes
   `LowerBound.two_mul_bits_lower_of_cubic_square_bound` together with
   `EncodingLowerBound.shapeCount_cubic_square_lower n`.

The last step is arithmetic on the variable-length capacity. It constructs no
fixed-length encoding and preserves the extra one bit in the bound.

## Exact bounded universe

`EncodingVariableLowerBound.boundedBitStrings 0 = [[]]`; the successor appends
the existing universe of exactly length `B+1`. The public cardinality theorem
conjoins all three facts:

```lean
(boundedBitStrings B).Nodup /\
  (boundedBitStrings B).length = 2^(B+1)-1 /\
  forall bits, bits \in boundedBitStrings B <-> bits.length <= B
```

Distinct lengths remain distinct list objects. The enumeration has no padding,
prefix-free restriction, hidden length tag, or exclusion of the empty list.
The length proof first establishes `length + 1 = 2^(B+1)` so natural-number
truncated subtraction cannot hide the zero boundary.

## Controls and their exact scope

- `emptyEncoding : ExactRMQBoundedEncoding 0 0` exhibits the empty input case.
  There is no valid nonempty window at size zero; this is explicit arithmetic.
- `singletonEncoding : ExactRMQBoundedEncoding 1 0` exhibits a nonempty
  valid-query domain at zero payload bits. Its fixed size-only advice is
  `n-1`; the only valid answer at size one is zero.
- `ofSizeAdvice` fixes `advice n` before obtaining the payload/endpoints-only
  decoder. Its exactness premise still quantifies over every size-n input.
- `input_domain_nonempty n` exhibits `List.replicate n 0` for every size.
- `query_ne_none`, `null_decoder_impossible`, and `wrong_answer_impossible`
  directly project this structure's `query_exact`, the same field consumed by
  the counting proof. They do not attack a sibling encoding predicate.
- `equal_key_leftmost E` forces answer zero for `[7,7]` and interval `[0,2)`.
- `two_input_codes_ne E` proves `[0,1]` and `[1,0]` must have different
  payloads at size two, by their different answers on that same valid interval.
- `zero_budget_two_impossible` uses the exact uniform length field to turn a
  zero budget into empty payloads, then uses that collision control.
- `constant_payload_exactness_impossible query` negates the full valid-window
  exactness premise, specialized to the constant empty payload and size two,
  for every fixed decoder. A decoder with additional input/shape advice would
  have a different type and does not satisfy this theorem's accepted predicate.

These kernel controls are sources for the parent-owned typed consumer and
replay registry. This leaf does not claim the mutation campaign has run.

## Proof digestion

Conceptually, the counting universe now contains all lengths up to one uniform
budget. The RMQ argument itself remains the existing leftmost-answer-to-shape
theorem. In plain English, one bit list and one fixed decoder cannot encode two
different Cartesian shapes, even if the decoder observes the list's length.

Live assumptions are the explicit uniform budget, exact answers on valid
nonempty half-open windows, ordinary `List Int` semantics, and a decoder fixed
across every size-n input. Payload bits and proof fields are separate; this
pure counting leaf makes no interpreter, trace, instruction-cost or native-time
claim. The parent's packed-allocation adapter supplies the named downstream
consumer `PackedWordRAM.packedAllocationOptimality_holds` at the actual memory.

A skeptical graduate student should ask whether the actual decoder is fixed
across all inputs and whether the counted serialized memory is exactly the
memory reconstructed before query execution. Those are the adapter's assigned
join obligations; no counting theorem here claims to establish them by itself.

## Verification ledger

- Skill preflight: PASS at the exact baseline/governance above, required
  `rmq-proof-sprint`, actual runtime catalog
  `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`.
- Source and Std-library inspection: completed read-only before drafting.
- `git diff --check -- RMQ/Core/EncodingVariableLowerBound.lean`: exit 0 during
  drafting; the new file was untracked, so final staged/range hygiene remains
  the parent's required check and is not certified by this command.
- Development-loop build, granted serialized slot: PASS on the first run.
  Command:
  `pwsh -NoProfile -File scripts/variable_payload_build.ps1 -Module RMQ.Core.EncodingVariableLowerBound -DeadlineSeconds 600`.
  The source closure contained 15 modules; 14 unchanged baseline modules reused
  the parent's task-local prerequisite artifacts, and this one source rebuilt.
  The actual child command was the pinned Lean 4.22.0 binary with `-j1`, output
  `.lake/build/lib/lean/RMQ/Core/EncodingVariableLowerBound.olean`, and input
  `RMQ/Core/EncodingVariableLowerBound.lean` at this worktree.
- Exact source SHA-256:
  `688E98C5FBCC12D17CB475FD4B381B707EC224805C9A3C1C0B1858B3270B1FFA`.
  Base remains the exact governance commit above; this source was an untracked
  addition at verification time, with parent-owned changes elsewhere.
- Evidence:
  `evidence/build-20260912T071953550.jsonl`.
  Platform: `Microsoft Windows NT 10.0.26200.0`.
  Child start: `2026-09-12T07:19:54.9855932Z`.
  Deadline: 600 seconds, with cold-module margin above the parent's just-passed
  baseline closure. Observed child duration: 18.991 seconds. Exit: 0.
  Standard output and error: both empty. TimedOut: false.
  Ownership: `kill-on-close-job`; no terminated child IDs and no output limit.
  No retry was needed. Slot returned to the parent immediately after completion.
- Covered propositions: all declarations above, including the full exact
  cardinality conjunction, shape injection, `shapeCount_le`,
  `doubledLogSlackLower_le`, and every generic control, were elaborated by that
  successful module build. Thus their exact source signatures quoted here are
  checked theorem types, not merely planned interfaces.
- The parent will additionally import the named declarations through its typed
  packed consumer and print their axiom inventories. This leaf build does not
  claim to execute the parent-owned replay registry, certify the full packed
  join, run aggregate gates, or establish independent acceptance. No POSIX
  process-ownership branch was exercised by this Windows build.
- Narrow trust hygiene on this source used
  `rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib|native_decide|Lean\.ofReduceBool" RMQ/Core/EncodingVariableLowerBound.lean`.
  Exit 1 with no output means no matches. The parent retains ownership of the
  required repository-wide scans and committed-range whitespace check.

## Follow-on leaf: independent validation consumer and runtime

Status: follow-on validation source elaborated after the resumed exclusive
grant; runtime execution remains parent-owned. The historical resource-wait
phase and the completed build evidence are both retained below.

New disjoint ownership: `RMQ/Validation/VariablePayloadLowerBound.lean` only;
append evidence in this note. The parent owns the producer, replay scripts,
lake target, matrix, ledgers, committed artifacts and build scheduling.

The validator freezes literal expected types in `checkO01` through `checkO16`
for all optimality fields, and `checkM01` through `checkM33` for all reconstructed
machine fields. These types are stored as ordinary Lean source and do not read
or regenerate from producer definitions during a replay. Every proof projects
`packedAllocationOptimality_holds` directly, using `.machine` for the second
group. `publicContract` and the independent conjunction `composedConsumer`
also consume that named theorem. Removing or changing a field cannot leave
only an unused record-construction check.

`genericLowerConsumer`, `genericCardinalConsumer`, and
`genericShapeCountConsumer` explicitly consume the generic named declarations.
`canonicalEncodingConsumer` fixes the canonical adapter's encode/query
projections to `allocationBits` and `allocationDecoder n`, then applies the
generic lower-bound theorem to that actual bounded encoding.

Definition pins independently spell out the generic length/exactness field
types, UniformAllocationBudget, serializer/deserializer, actual allocation
bits, decoder argument list/body, reconstructed memory, adapter encode/query
projections, Memory, Program, Instruction.Fits, State.Fits, Instruction.Safe,
ValidRange, LeftmostArgMin, and LittleOLinear. The generic pins use a literal
typed `show` expression before the definitional-equality proof, so a weaker
field is rejected at the expected proposition.

The exact runtime registry is `LB1-RUNTIME-V1`:

- `R01-EMPTY`: actual allocation reconstruction and empty/oversized queries.
- `R02-SINGLETON`: actual decoder returns literal zero; invalid endpoint rejects.
- `R03-LEFTMOST`: actual decoder returns literal zero for two equal keys, also
  checked against the independent ordinary scan specification.
- `R04-ZERO-LENGTH`: empty serialization/deserialization, plus a deliberate
  zero-width collision demonstrating why positive width guards are required.
- `R05-ZERO-WORDS`: distinct bit lists for zero, one and two zero words; exact
  reconstruction and a full bounded word-list round trip.
- `R06-SAME-SHAPE`: distinct values `[0,1]` and `[9,10]` share the actual numeric
  memory and bit list and have the independently expected zero answer.

Registry identity, nonemptiness and duplicate-freedom have kernel proof
declarations in the draft and runtime checks. Default selection runs the full
registry. `--list` prints only the frozen version/IDs/count. `--case ID` must
select exactly one known case. Empty, whitespace, malformed, unknown, missing
and duplicate argument forms raise distinct or explicit selection errors.
The optional environment channel `LB1_RUNTIME_SELECTOR=case:<ID>` preserves
an explicitly empty ID as `case:` on native hosts that otherwise drop empty
arguments. It cannot be supplied together with command arguments.

Every actual allocation is prepared inside the selected case through a
`noinline` IO helper returning both bits and numeric memory. This keeps the
large construction behind case selection and prevents closed fixture payloads
from becoming new eager module-initialization constants. The imported PQ1
program remains the accepted producer's definition. The direct actual
`allocationDecoder` is used; no array evaluator or unrelated implementation
substitutes for it. Runtime cost has not yet been measured.

Kernel boundary consumers instantiate the named actual decoder exactness field
at empty, singleton, equal-key and invalid-endpoint inputs. The word round-trip
and injectivity controls project the same public fields. Runtime evidence and
field/proposition mutation replay remain pending; none is represented as passed
by the existence of these definitions.

### Validation phase return: resource wait

Status: INCOMPLETE. Exact phase: `VALIDATION_DRAFT_WAITING_FOR_ADAPTER_BUILD`.
Unmet local evidence: Lean elaboration of the 49 exact-type consumers and pins;
runtime startup/listing, one known selector and the full six-case registry;
selector-negative execution. The parent separately owns the mutation campaign,
axiom inventory, final gates and full acceptance-row closure.

The adapter owner reports build session `43327`, started
`2026-09-12T07:24:55Z`, still preparing the cold 251-module dependency closure
and passing completed modules (approximately 60 completed at its update).
That is scheduling evidence from the owner, not a completed validation command
or a gate verdict. No second Lean/Lake process was started.

Resume this validation leaf when the adapter has elaborated and the parent
grants the serialized slot. The first command should be the existing bounded
build wrapper for `RMQ.Validation.VariablePayloadLowerBound`; diagnose and
repair only this owned validation file. Then run bounded `--list` and one
known runtime case before the full registry. If direct actual decoding is
slow, first measure the actual owned process; any array-backed alternative
must carry a checked equality to this actual allocation decoder before use.

### Validation compilation resumed and passed

Status: assigned validation compilation leaf passed. The whole LB-1 campaign
still requires parent-owned runtime/replay, trust inventory, final hygiene,
independent audit and coordinator acceptance.

The parent granted exclusive Lean ownership after the adapter's 251-module
closure had passed. The resumed scope was compilation and repair only, with
the runtime startup/known selector/full suite explicitly reserved to the parent.
No runtime suite or root-owned script was run by this leaf.

Exact development command for both attempts:

`pwsh -NoProfile -File scripts/variable_payload_build.ps1 -Module RMQ.Validation.VariablePayloadLowerBound -DeadlineSeconds 1800`

First attempt:

- Evidence: `evidence/build-20260912T084243070.jsonl`.
- Source SHA-256:
  `0C2C86D986312DB6A4012BE2C0E5CE69625A5729042553E842D68313C8594D7E`.
- Child start: `2026-09-12T08:42:46.4493011Z`.
- Exit 1 after 35.757 seconds; no timeout and empty stderr.
- The sole reported error was the final goal of `sameShapeBitsConsumer`:
  `serializeWords (wordWidth [0,1].length) (buildMemory [9,10]) =
   serializeWords (wordWidth [9,10].length) (buildMemory [9,10])`.
- Material repair: add a final `rfl` after the same-memory rewrite, explicitly
  discharging the definitional equality of the two length-two inputs. No
  expected type, producer field, contract or runtime behavior changed.

Second attempt:

- Evidence: `evidence/build-20260912T084355841.jsonl`.
- Exact passed source SHA-256:
  `20B076D0BDB84703D7238D196BD13832B3A7BFAB411CB5DF56BD685B855CA394`.
- Child start: `2026-09-12T08:44:01.0131674Z`.
- Exit 0 after 32.69 seconds, no warnings/errors, stdout/stderr both empty,
  no timeout, no output-limit event and no terminated child IDs.
- Platform: `Microsoft Windows NT 10.0.26200.0`.
- Direct child: pinned Lean 4.22.0 with `-j1`; output was task-local
  `.lake/build/lib/lean/RMQ/Validation/VariablePayloadLowerBound.olean`.
- Complete closure: 252 modules; 251 unchanged prerequisites reused from the
  passed parent/adapter closure, and only this source rebuilt. The 1800-second
  per-module deadline came from the parent's explicit grant and included
  substantial cold-import margin. Actual compilation needed 32.69 seconds.
- Process ownership: `kill-on-close-job`. Both wrapper sessions ended. The
  exclusive slot was explicitly released to the parent after the passing
  command returned; no owned Lean process remains.

Every source theorem in the validation file was checked on the second attempt.
The checked surface includes all 16 `checkO` expected types, all 33 `checkM`
expected types, `publicContract`, `composedConsumer`, three named generic
consumers, all definition pins, `canonicalEncodingConsumer`, exact decoder
empty/singleton/equal-key/invalid-endpoint instances, word round-trip and
multiplicity controls, same-shape memory/bits, and the exact/nonempty/Nodup
runtime registry declarations. The executable definitions and global `main`
also elaborated, but elaboration is not runtime evidence.

Proof digestion: the client now states the entire advertised field surface
literally and obtains each proof from the one named packed optimality theorem.
The definition pins make the new payload and decoder formulas reviewable at
their actual function arities. The only compilation repair made explicit a
two-list length equality; it introduced no new mathematical assumption. A
skeptical reader's next question is whether source mutations actually fail
these same expected propositions and whether the executable registry runs
the decoded memory path. Those remain the parent's assigned replay/runtime
checks, not claims established by this successful compilation.

## S03 consumer elaboration repair

Status: baseline-checked minimal candidate; the root must run the existing
clean-tree `S03-SIBLING-BUDGET` replay after committing. This diagnostic is not
recorded as an authoritative replay pass or a complete campaign verdict.

Repair base: `d6dabbec10648f368df9ddcd32102f84deffb281`. At that source the V3
campaign reached S03 after 60 successful controls. The raw producer stage
returned exit 0 in 4.276 seconds. The raw consumer stage returned exit 1 after
16.226 seconds with `maximum recursion depth has been reached` at `checkO09`,
so that outcome was inconclusive rather than semantic rejection. The raw
records were inspected at
`.lake/lb1-replay/20260912T090642898/S03-SIBLING-BUDGET-{producer,consumer}.json`;
the root subsequently preserved the campaign under
`evidence/replay-v3-d6dabb-inconclusive`.

The expected proposition P is unchanged:

```lean
forall n B, UniformAllocationBudget n B -> shapeCount n <= 2^(B+1)-1
```

The existing mutation's proposition Q is unchanged:

```lean
forall n B, UniformAllocationBudget n B ->
  shapeCount n <= 2^(2*n+allocationRho n+1)-1
```

The only source change is the proof body of `checkO09`:

```lean
by with_reducible exact packedAllocationOptimality_holds.uniformBudgetCount
```

Core Lean 4.22.0 supplies `with_reducible`; no import, tactic extension, lemma,
expected type, guard, quantifier, field inventory, runtime case, or registry
changed. The restriction prevents ordinary definitional equality from
unfolding the large allocation residual while trying to identify Q with P.
Raising the recursion limit was rejected: it would permit more irrelevant
unfolding and would not address the semantic failure boundary. The original
producer's exact field type already matches P without that unfolding.

Baseline verification:

- Command:
  `pwsh -NoProfile -File scripts/variable_payload_build.ps1 -Module RMQ.Validation.VariablePayloadLowerBound -DeadlineSeconds 600`.
- Full validation module accepted: 252-module closure, one rebuilt module,
  exit 0, 42.411-second owned Lean child, no output or stderr, no timeout.
- Exact source SHA-256:
  `092B965AB266D1578A1CDD83A05BAC31644F14CE4400C380CD78032EA5850B72`.
- Evidence: `evidence/build-20260912T100805553.jsonl`; child start
  `2026-09-12T10:08:08.5576461Z`; pinned Lean 4.22.0 `-j1`, task-local cache,
  Windows `10.0.26200.0`, `kill-on-close-job` ownership.

Ignored scratch diagnostic:

- Source: `.lake/lb1-s03-repair/SamePredicateDiagnostic.lean`.
- Output: `.lake/lb1-s03-repair/SamePredicateDiagnostic.json`.
- It imports the intact packed producer, derives exactly Q from the existing
  canonical count field, and tries to use Q at exactly P with the repaired
  proof-elaboration setting. Every n/B/budget quantifier is retained. It is a
  same-proposition elaboration diagnostic, not a substitute field mutation.
- The bounded direct pinned Lean `-j1` command was run sequentially through
  `Invoke-RMQOwnedBoundedProcess`, with a 600-second deadline and no output
  olean argument. Exit 1 after 7.524 seconds, with an explicit `type mismatch`
  listing Q as the actual type and P as the expected type. No recursion-depth,
  timeout, output-limit or stderr event occurred.
- No producer source or compiled artifact was overwritten by the diagnostic,
  so it needed no mutation restoration. Its files are under ignored `.lake`.
  The baseline build updated only the normal validation artifact/cache key.
- Both owned sessions completed; the sole Lean slot was explicitly released
  to the root immediately afterward. No focused/full replay was started by
  this leaf. Working-tree `git diff --check` passed.

Proof digestion: the mathematical proposition is identical. The client now
compares the promised bound without expanding unrelated implementation data.
In plain English, a theorem about the canonical allocation budget must fail
when asked to justify an arbitrary uniform budget. No assumptions were added.
The next skeptical check is the root's unchanged S03 mutation against the
actual altered public field, followed by the frozen full campaign and fresh
audit; the isolated diagnostic alone does not close those obligations.
