# Proof Acceptance Matrix Template

Freeze this matrix before implementation. Prompt requirements and coordinator-
assigned inherited IDs do not change after work starts unless the coordinator
records an explicit contract amendment. Evidence and status may evolve.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Falsifier or edge case | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `REQ-01` | Copy prompt text verbatim. | Local or roadmap | State the conclusion that would entail it. | Name every link to the consumer. | Name a concrete way this could be false. | Quote the checked theorem type/result; a name alone is insufficient. | Open |
| `INV-...` | Copy the assigned invariant from `COMPLETION_GATE.md`. | Inherited | State the required conclusion for this target. | Identify the exact object(s). | Include tiny/threshold/dead cases as applicable. | Fill after proof/check. | Open |
| `CHK-01` | Copy the requested command. | Verification | Exit success plus relevant output. | Name the surface covered. | State important uncovered scope. | Fill after running. | Open |

Rules:

1. A row is closed only when the evidence conclusion entails the exact
   requirement for the named consumer.
2. If two claims concern different payloads, stores, executions, widths, or
   queries, show a proved identity/equivalence chain or leave the row open.
3. For Lean evidence, quote the theorem type or list every hypothesis and
   conclusion. Do not substitute a declaration-name inventory.
4. Record counterexamples attempted and edge cases exercised. A passing build
   is not semantic evidence for a requirement.
5. Keep local-rung and roadmap-node rows distinct.
6. The worker may report `CANDIDATE_COMPLETE`; only the coordinator records
   `ACCEPTED`, and designated public capstones also require fresh blind audit.
