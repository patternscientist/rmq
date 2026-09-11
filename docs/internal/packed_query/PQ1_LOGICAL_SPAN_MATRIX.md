# PQ1-LS frozen acceptance matrix

Base: 9e2720b991e203d22a2787abf66dbfb9888088fb. Governance: 4639223bc8130b0ef752270b5cbdd74325abcd60. Branch: codex/fully-charged-packed-query-v1. Scope: scalar logical span geometry and same-allocation value/length refinement. No staging/commits.

## Verbatim frozen requirements

- REQ-LS-GEOMETRY: reviewerLogicalSpan (n lc sc segment index : Nat) : Option NumericSpan is a proof-free scalar geometry specification. For segment20 use the existing interior classifier and its closed bit address/read width. For every other segment<23 use regularDescriptor's four fields (base,bits,stride,count) through regularSpan; outside23 return none. Prove this span produces the old packedReviewerLogicalPlan via old-width spanPlan and old decode expression, for every n/counts/segment/index, with exact value and logical length on canonical memory. Prove each present span length<=oldWidth and handle zero-width positions without a false end-of-memory premise.

- REQ-LS-RECOVERY: Prove universal direct bit-span recovery from repackWords headers W old for positive W, len<=W and position+len<=old.flatten.length (or len=0), not just aligned old cells. The decoded result is bitsToNatLE ((old.flatten.drop position).take len), using decodeSpanNat W (headers.length*W+position) len on that same memory. Numeric physical cells remain raw and no double-width runtime concatenation appears.

- REQ-LS-CANONICAL: Define directLogicalReadNat n lc sc memory segment index using reviewerLogicalSpan; for some span, decodeSpanNat (wordWidth n) (metadataWordCount*wordWidth n+span.position) span.length memory and return (decoded,span.length), otherwise none. For every canonical shape and every segment/index, prove it equals the canonical global ReadStore reply mapped to (bitsToNatLE bits,bits.length), and consequently the existing packedReviewerLogicalRead reply under a request with those segment/index fields. No successful-read, readiness, count-zero, one-macro, one-word-entry, or minimum-size hypothesis. Expose descriptor equations the lead's source assembler can consume.

- CHK-LS-LEAN: Narrow checks, exact-type consumer over every canonical segment/index, empty/singleton and dead-interior/empty-sentinel typed consumers. Do not use fixtures as universal evidence or native_decide.

- `INV-STORE-IDENTITY`: the exact payload/store executed is the payload/store
  counted by the public space theorem; a theorem about a sibling payload is
  insufficient;

- `INV-VALUE-DEPENDENCY`: returned values and routing decisions depend on
  actual charged reads, not a semantic answer computed before the reads. When
  the requirement concerns the returned answer or route, evidence must constrain
  that value, state, or route; inequality of an enclosing trace record can be
  satisfied by its log alone and is insufficient;

- `INV-PROOF-SEPARATION`: proof-only fields never carry answers or uncharged
  routing information;

- `INV-READ-BACKING`: every successful read is backed positionally by the
  counted store;

- `INV-ALL-SIZE`: exactness covers all assigned sizes and edge cases without
  hidden readiness or compatibility dispatch;

## Frozen definitions and evidence matrix

reviewerLogicalSpan n lc sc segment index uses regularDescriptor fields through regularSpan for every segment<23 except20, classifier closed position/width for20, none outside23. directLogicalReadNat uses that span and decodeSpanNat over metadataWordCount-prefixed new-width memory, returning Option(Nat*Nat) for value and logical length. No semantic memory is an executable argument.

| ID | Exact evidence and consumer chain | Anti-vacuity challenge | Status |
| --- | --- | --- | --- |
| REQ-LS-GEOMETRY | `reviewerLogicalSpan_old_geometry` proves old plan equals `(span.map (spanPlan oldWidth)).getD []` and every old decoder equals `span.map (packedReviewerDecodeSpan n position length cells)`. `reviewerLogicalSpan_length_le` proves present `span.length ≤ packedReviewerCellWidth n`. Descriptor equations quoted in report feed Locate. | All 23 branches and outside range are proved; arbitrary interior indices use first successful component with exact entry/chunk geometry. Zero-length sentinel theorem imposes no endpoint bound. | Closed |
| REQ-LS-RECOVERY | `decodeSpanNat_repacked_span`: positive W, len≤W, fitted span OR len=0 imply `decodeSpanNat W (headers.length*W+position) len (repackWords headers W old) = some (bitsToNatLE ((old.flatten.drop position).take len))`. | Universal positions include unaligned/crossing spans. `len=0` branch accepts positions beyond allocation; no false endpoint premise. | Closed |
| REQ-LS-CANONICAL | `directLogicalReadNat_eq_globalReadStore`: every shape/segment/index on `shapeMemory shape` equals global `readWord?` mapped to `(bitsToNatLE bits,bits.length)`. `directLogicalReadNat_eq_reviewer` gives the exact older logicalRead map for every request. | Present empty sentinel is `some (0,0)`; dead interior is `none`. No successful-read, nonzero-count, one-word-entry, or size premise. | Closed |
| CHK-LS-LEAN | Whole owned module emits clean artifacts. `logicalSpan_canonical_consumer` independently spells the all-shape/global reply type; empty and singleton consumers retain arbitrary segment/index, dead-interior and empty-sentinel consumers pin independent expected replies. | Kernel-checked general theorems supply universal evidence. Named boundary consumers constrain presence/absence without native evaluation. | Closed |
| INV-STORE-IDENTITY | `shapeMemory shape = repackWords (metadata shape) (wordWidth shape.size) (packedReviewerMemory shape)` by definition; `metadata_length` proves prefix174. This is the literal argument of both canonical equality and `shapeMemory_capacity_le`. `buildMemory xs` wraps this same object. | No sibling-store equality or same-length proxy appears in the composition. Exact object chain and proposition arguments are quoted in report. | Closed |
| INV-VALUE-DEPENDENCY | Executable `directLogicalReadNat` binds scalar geometry to `decodeSpanNat` of its supplied numeric memory; only the decoder value is mapped to `(value,length)`. Canonical theorem constrains that exact returned option. | Ignoring the decoder value or replacing presence by a length-only result fails the pinned equality; empty-sentinel and dead-interior expected types separate `some (0,0)` from `none`. No mutation campaign claimed. | Closed |
| INV-PROOF-SEPARATION | Definitions take only five Nat scalars and List Nat memory. Shape, old bit lists, and a long proof-side false window appear only in proofs; there is no proof field or semantic answer argument. | The proof-side synthetic window is consumed only to infer requested length from the old universal word-width theorem, never by executable decoding. | Closed |
| INV-READ-BACKING | `reviewerLogicalSpan_canonical_fits` derives positive-span end bounds from old canonical plan-address theorem, while `decodeSpanNat_repacked_span` uses dense numeric cells of the same flattened old memory. `decodeSpanNat` loads memory[q]? and only when crossing memory[q+1]?. | Zero-length spans do no physical load. The proof never equates old/new physical occurrences; the exact new receipt story stays with SpanAssembly. | Closed |
| INV-ALL-SIZE | Canonical equality and its consumer quantify over every CartesianShape and all Nat segment/index values. Scalar geometry also quantifies over arbitrary lc/sc, not only canonical or zero counts. | Exact empty/singleton universal consumers, arbitrary-shape dead interior, and empty-alias success check. Multi-chunk interior formula retains div/mod and final short width for all component sizes. | Closed |

## Verification plan

Standalone Lean against local copied artifacts, one explicitly transferred build slot. Final owned-source hygiene, strict UTF-8 frozen-block equality, and new-file whitespace. Lead owns strict design-policy and committed-range checks after integration. No mutation campaign or whole-machine claim assigned.

| Role | Command/surface | Distinct coverage and tree | Outcome |
| --- | --- | --- | --- |
| Preflight | `project_skill_preflight.ps1` at governance4639223, proof-sprint required, actual three-skill RMQ catalog | Canonical governance and runtime role availability before edits; unchanged HEAD9e2720b shared worktree | PASS |
| Development | Standalone Lean `LogicalSpan.lean` against local artifacts | Recovery, descriptor geometry, old-plan cases, canonical equality | Initial broad classifier simplification hit heartbeat limit; replaced by abstract eight-count arithmetic. Branch reduction fixed. Final empty-alias simplification fixed. |
| Final-required | `lean -o .../LogicalSpan.olean -i .../LogicalSpan.ilean RMQ/Core/WordRAM/Packed/LogicalSpan.lean` | Final source SHA256 `ad3dc3b45b4f9967ca6ad7b1a66f018b0a9532fbb82958a3185796692bef82d6`; all nine rows, all named typed consumers | Exit 0, no diagnostics, approximately 10 seconds. Only one Lean process. |
| Final-required | Imported canonical/descriptors exact-type consumers and eight theorem dependency inventories | Independent import of final LogicalSpan artifact; exact public propositions and trust footprint | Exit 0 in 6.04 seconds; inventories contain only propext, Classical.choice, Quot.sound. |
| Final-required | Exact UTF-8 frozen-block equality | Four prompt rows and five inherited gate blocks; no locale conversion or whitespace normalization | Nine exact byte comparisons PASS before final module check and after matrix completion. |
| Final-required | Required repository hygiene/native scans and `git diff --check` | Mathlib/trust escape tokens and tracked whitespace; source-only change with no new runtime/trust primitive | No token matches; whitespace PASS. New owned-file no-index checks reported no whitespace errors; exit 1 is ordinary content difference. |
| Proportionate omission | Full lake build, aggregate gate, executable mutation replay | Narrow proof leaf; no changed broad root or campaign. Lead owns later combined integration and committed-range/design gates. | Skipped with contract scope recorded. |

## Template policy

# Proof Acceptance Matrix Template

Freeze this matrix before implementation. Prompt requirements and coordinator-
assigned inherited IDs do not change after work starts unless the coordinator
records an explicit contract amendment. Evidence and status may evolve.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `REQ-01` | Copy prompt text verbatim. | Local or roadmap | State the conclusion that would entail it. | Name every link to the consumer. | Attempt a concrete way this could be false and name what rejects it. | Quote the checked theorem type/result; a name alone is insufficient. | Open |
| `INV-...` | Copy the assigned invariant from `COMPLETION_GATE.md`. | Inherited | State the required conclusion for this target. | Identify the exact object(s). | Include semantic mutations and tiny/threshold/dead/invalid cases as applicable. | Fill after proof/check. | Open |
| `CHK-01` | Copy the requested command. | Verification | Exit success plus relevant output. | Name the surface covered. | State important uncovered scope. | Fill after running. | Open |

Rules:

1. A row is closed only when the evidence conclusion entails the exact
   requirement for the named consumer.
2. If two claims concern different payloads, stores, executions, widths, or
   queries, show a proved identity/equivalence chain or leave the row open.
3. For Lean evidence, quote the theorem type or list every hypothesis and
   conclusion. Do not substitute a declaration-name inventory.
4. Record counterexamples and semantic mutations actually attempted for every
   applicable semantic subclaim, their outcomes, and the theorem or definition
   that rejects them. Merely naming one easy falsifier for a bundled row is not
   enough. A passing build is not semantic evidence for a requirement.
5. Keep local-rung and roadmap-node rows distinct.
6. The worker may report `CANDIDATE_COMPLETE`; only the coordinator records
   `ACCEPTED`, and designated public capstones also require fresh blind audit.
7. For liveness, coverage, ownership, dependency, and composition rows, expand
   load-bearing definitions. A predicate made true by definition, a manually
   restated enumeration, aggregate-record inequality caused only by its log, or
   guarded/unguarded object mismatch leaves the row open.
8. Projection-specific evidence must match the quantification and validity
   domain of the requirement. A singleton executable witness does not close a
   universal dependency row.
9. Every semantic mutation row must record the accepted predicate `P`, the
   rejected predicate `Q`, and all guards and quantifiers. Require `P = Q` or a
   checked implication `P -> Q`; otherwise leave the row open.
10. Distinguish component may-read, component successful-read, top-level
    reachable-read, and actual emitted-occurrence claims. Evidence at one level
    does not silently entail another.
11. For provenance rows, state whether evidence preserves only event values or
    also occurrence position, multiplicity, producing instruction, folded
    pre-state, and invocation parameters. `List.Mem` alone is event-value
    evidence.
12. A worker cannot narrow a row by calling residual work "strictly stronger"
    or future hardening. Record an explicit coordinator-approved contract
    amendment or keep the row open.
13. For classifier/linter rows, finite fixtures are lower bounds. Freeze the
    category boundary, add category-level holdouts and allowance-bypass
    mutations, and test the production final verdict across supported path and
    parser shapes. A copied regex or whole-file bypass cannot close the row.
14. For small-step machines, inspect evaluator bodies. A constructor/category
    inventory plus one step per constructor does not close atomicity when one
    branch hides recursion, variable-length work, or several primitive
    categories.
15. Expected executable results must come from an independent specification;
    an implementation result cannot serve as its own test oracle.
16. Width evidence must enumerate every encoded constructor field, including
    dormant instructions, register identifiers, and control-flow operands.
17. Account for input-dependent constants stored in program code, and verify
    that executable validators import and mutate the new layer rather than only
    its predecessor.
18. After the final commit, run `git diff --check <exact-base>..HEAD`; a clean
    working tree alone does not certify committed whitespace.
19. For mandatory public-certificate fields, name a checked typed consumer that
    projects every exact field proposition and object argument. Record
    field-deletion, proposition-weakening, and sibling-substitution mutations;
    opaque record passage and constructor initialization do not establish
    anti-bypass consumption.
20. If closure cites a mutation campaign, identify the committed runner or
    stable fixtures, exact cases, expected verdict/failure surface, expected-
    accept controls, and restoration/clean-tree check. Report-only experiments
    and unreferenced Git objects leave `INV-MUTATION-REPRODUCIBILITY` open.
    For a public dependency, pin an expected type independently of the current
    theorem declaration and mutate the public proposition itself.
21. If the worker stops on an obstruction, put the exact frozen target and the
    obstruction proposition side by side, including domains, objects, guards,
    and quantifiers. Require a checked target negation or target-to-`False`
    implication. Separate arbitrary-state, shape-growth, and singleton-
    reachability witnesses need a checked bridge into one canonical reachable
    family; prose composition leaves the target row open. State whether the
    result obstructs only the current implementation/decomposition or every
    construction allowed by the contract.
