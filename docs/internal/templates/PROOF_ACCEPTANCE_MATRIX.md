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
