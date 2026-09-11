# PQ1-S frozen acceptance matrix

Base/governance: 4639223bc8130b0ef752270b5cbdd74325abcd60. Branch: codex/fully-charged-packed-query-v1. Scope: numeric functional decoder and exact repacked loader. Primitive execution is the lead-owned subsequent consumer. No staging or commits.

## Verbatim frozen requirements

- REQ-S-SPAN: Define spanPlan width position len as zero addresses for len=0, one for a contained nonempty span, two consecutive addresses for a crossing. Define decodeSpanNat on List Nat only, using each planned numeric cell and scalar shift/division/remainder/mask arithmetic. For positive width, uniform full-width bit cells, len<=width and position+len<=cells.length*width, prove decoding their numeric map returns some(bitsToNatLE(cells.flatten.drop position |>.take len)). Include the zero-length endpoint at the end of memory. Missing required physical cells return none.

- REQ-S-REPACK: Define loadOldCellNat headerCount width oldWidth oldCount memory index with only numeric scalars/memory. Guard index<oldCount, read span headerCount*width+index*oldWidth of length oldWidth. For every numeric header list fitting width, every old bit-cell list uniformly oldWidth, and 0<oldWidth<=width, prove loadOldCellNat headers.length width oldWidth old.length (repackWords headers width old) index = (old[index]?).map bitsToNatLE for every index. No shape, old-memory oracle, proof field or desired reply may enter the executable loader.

- REQ-S-PLAN: Prove the plan length<=2, exact read backing and preservation of missing/zero-length cases at this functional read layer. State clearly that primitive instruction execution is the lead's later consumer, not established by a pure decoder theorem.

- CHK-S-LEAN: Elaborate Span.lean and kernel-checked concrete consumers for noncrossing, crossing, final padded cell, zero-length end, absent required physical read, absent old-cell index and all-ones raw cell without +1 overflow.

- `INV-STORE-IDENTITY`: the exact payload/store executed is the payload/store
  counted by the public space theorem; a theorem about a sibling payload is
  insufficient;

- `INV-VALUE-DEPENDENCY`: returned values and routing decisions depend on
  actual charged reads, not a semantic answer computed before the reads. When
  the requirement concerns the returned answer or route, evidence must constrain
  that value, state, or route; inequality of an enclosing trace record can be
  satisfied by its log alone and is insufficient;

- `INV-READ-BACKING`: every successful read is backed positionally by the
  counted store;

- `INV-PROOF-SEPARATION`: proof-only fields never carry answers or uncharged
  routing information;

- `INV-NO-SYNTHETIC`: synthetic events, decorative rereads, and post-hoc replay
  do not support the execution claim;

- `INV-CATEGORY-SEPARATION`: payload bits, proof fields, model ticks, machine
  state, Lean runtime, and measured performance remain distinct.

## Evidence matrix

| ID | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge | Evidence/status |
| --- | --- | --- | --- | --- |
| REQ-S-SPAN | Positive width, uniform cells, len ≤ width, span within flattened capacity imply decodeSpanNat numeric-map = some numeric flatten slice. | Uniform bit cells → positional numeric cells → scalar decoding → loadOldCellNat_repacked. | Contained/crossing/final padding; zero length at end. | CLOSED. `decodeSpanNat_uniform`: for every cells, width, position, len with 0 < width, every cell length = width, len ≤ width, position + len ≤ cells.length * width, the exact decoder on `cells.map bitsToNatLE` equals `some (bitsToNatLE ((cells.flatten.drop position).take len))`. Checked contained result 2, crossing 7, padded final old-cell 6, and zero-length endpoint 0. |
| REQ-S-REPACK | Every index: loadOldCellNat on exact repackWords = old[index]?.map bitsToNatLE. | Same repackWords counted by lead-owned capacity theorem → decodeSpanNat → original-cell option. | Header offset, invalid index, arbitrary old bits. | CLOSED. `loadOldCellNat_repacked`: uniform oldWidth and 0 < oldWidth ≤ width imply, for every index, the literal loader on `repackWords headers width old` equals `(old[index]?).map bitsToNatLE`. All numeric header lists are covered; no header-value bound is necessary for this proof because their values are unread. The checked expected-type consumer expands the allocation to `headers ++ denseWords width old.flatten`. |
| REQ-S-PLAN | Plan has ≤ 2 entries, successful decode iff all planned reads present, result preserved by positional agreement. | spanPlan and decodeSpanNat use identical guards and indices. | Missing first/second cells, zero-length no reads. | CLOSED. `spanPlan_length_le` proves length ≤ 2 without premises. `decodeSpanNat_isSome_iff` proves successful decode iff every geometric-plan reply is present. `decodeSpanNat_read_backing` retains an occurrence index and proves existence of the exact memory reply. `decodeSpanNat_none_of_missing` proves any absent required occurrence forces none. `decodeSpanNat_congr` proves full option equality from positional plan agreement. First/second missing and zero-length examples pass. A failed first read short-circuits; the geometric plan is not asserted to be an actual failure trace. |
| CHK-S-LEAN | Standalone Lean elaboration and seven kernel examples; hygiene and working whitespace check. | Changed Span.lean and its concrete consumers. | Explicit numeric expected values independent of implementation. | CLOSED. Final standalone Lean emitted Span.olean with exit 0 and no warnings in 5.30 seconds. Ten direct examples plus named returned-value dependency and independent expected-type consumer elaborate. Owned-file hygiene, frozen-requirement verification, and whitespace checks are recorded in the report. |
| INV-STORE-IDENTITY | Loader theorem uses literal repackWords headers width old. | Same DensePacking definition used by capacity theorem. | Sibling allocation substitution. | CLOSED at the assigned functional layer. Exact same `repackWords` term appears in the capacity theorem and the universal loader theorem; the expected-type consumer spells out its headers/denseWords body. The final padded fixture uses the constructor itself, so dropping the header-offset relationship or substituting arbitrary sibling contents is incompatible with the stated equality. No whole-machine composition claim is made. |
| INV-VALUE-DEPENDENCY | Decode agreement from exactly planned positional cells plus direct result-change boundary witnesses. | Numeric replies → scalar decoded value, never a semantic callback. | Mutate consumed bit and inspect returned option. | CLOSED at the assigned functional layer. `decodeSpanNat_congr` compares the entire Option Nat projection. `crossing_value_dependency` proves the original crossing result differs when first reply 13 changes to 5 and when second reply 3 changes to 2. These literal alternatives return 6 and 5 versus 7. No claim that every bit mutation changes every result is made. |
| INV-READ-BACKING | For every planned occurrence, successful decode requires corresponding memory[index]? present. | Ordered spanPlan indices → List.getElem? replies. | Remove either required cell. | CLOSED. For every occurrence < plan.length, successful decoder implies `exists word, memory[plan[occurrence]]? = some word`. Missing physical first or second cell yields none. The statement preserves occurrence indexing, and the plan definition fixes order and consecutiveness. |
| INV-PROOF-SEPARATION | Executable definitions take only Nat scalars and List Nat. | Proof hypotheses appear only in refinement theorems. | Inspect definition arguments. | CLOSED. `spanPlan` takes three Nat scalars; `decodeSpanNat` takes three Nat scalars and List Nat; `loadOldCellNat` takes four Nat scalars, List Nat and the Nat index. Bit lists and uniformity proofs occur only in specification/refinement arguments. No shape, source input, semantic reply, callback, or proof field is an executable argument. |
| INV-NO-SYNTHETIC | Functional plan and option reads match guard/case structure. | No execution trace or charge asserted in this leaf. | Zero-length performs no reads. | CLOSED for the expressly assigned functional read layer. Definition inspection shows the returned value is built inside numeric getElem? binds. Zero length returns some 0 before any bind; contained spans bind one read and crossings bind a second read after the first succeeds. No event list or post-hoc replay is presented as execution evidence. |
| INV-CATEGORY-SEPARATION | Documentation explicitly scopes decoder theorem to functional representation refinement. | Lead later proves primitive execution, widths, step count. | No primitive budget claimed by this module. | CLOSED. Source documentation and report distinguish functional representation/absence theorems from primitive execution and accounting. No machine cost, native runtime, or complete capstone claim is attached to this leaf. |

## Verification plan

Development-loop: standalone Lean against local copied cache, one process at a time, to close all REQ-S and CHK-S-LEAN rows. Expected runtime is seconds after warm imports; inspect any live session before retries. Final-required leaf checks: owned-file hygiene and git diff --check. Lead owns exact-base strict design check and committed-range whitespace after integration. No mutation campaign or full build is claimed.

## Template policy

The full matrix policy used to freeze this contract follows.

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
