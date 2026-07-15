# A06 Blind Audit: Canonical RMQ Publication Cleanup

## Verdict

**REJECT**

Audited repository commit:
`95b5bc255475400c0f9d96c2b3a3f16de89bc128`.

Audit branch: `codex/a06-u3-docs-clean-reset-audit`.

This verdict was reconstructed from the checked theorem types, their immediate
dependencies, the narrow paper/headline import topology, and the named
reader-facing documents. Worker chats, W22, prior audit verdicts, and worker
completion reports were not used to form the verdict. Green scripts were
treated as supporting checks rather than semantic proof.

## Findings

### P0

None.

### P1

None.

### P2. Stale dated snapshot duplicates the current publication story

`docs/FAMILY_SUMMARY.md:136` starts a second narrative with
`Snapshot: 2026-07-01`, immediately after the new canonical current summary at
lines 3-133. The dated section is not marked frozen or historical, and it was
partly rewritten by the audited commit to make current claims: lines 174-199
describe the canonical all-size trace and call the `76` alias current, while
lines 200-230 continue the present list-facing/store-facing story.

This is stale lifecycle metadata attached to a duplicated current-status
narrative. It leaves two reader-facing explanations of the publication state
inside a required current document and therefore fails the requested clean
reset. This is not a stylistic preference: a reader cannot tell whether the
July 1 snapshot is frozen history or another authoritative current summary.

### P2. Canonical headline comments retain worker-phase vocabulary

The narrow current headline module still describes two canonical declarations
with worker-phase labels:

- `RMQ/Headlines/RMQ.lean:562` calls the current reviewer-manifest alias a
  `W19` packet.
- `RMQ/Headlines/RMQ.lean:612` calls the current footprint-transfer theorem a
  `U3` theorem.

These comments are on declarations imported by `RMQPaper`, not inside
`RMQ.Headlines.RMQCompatibility` or an explicitly historical document. The
checked declarations themselves are current and sound, but their reader-facing
descriptions fail the explicit requirement that current prose contain no
worker-phase vocabulary.

### P3

None.

## Adversarial Checks

1. **Canonical join: PASS.**
   `RMQ/Core/SuccinctFinalRAM.lean:9366-9440` conjoins the canonical reviewer
   payload bound, physical-word erasure, successful-read physical backing, the
   same canonical global trace, genuine-event/no-synthetic facts, cost and
   certificate bounds by `76`, and exact valid-query `scanWindow` answers.
   Its proof at lines 9441-9486 supplies those conjuncts from the corresponding
   concrete theorems. The literal cost reduces to `76` at lines 8634-8671.

   The list theorem at `RMQ/Headlines/RMQ.lean:68-153` conjoins
   `queryCost = 76`, little-o overhead, payload length, physical erasure,
   invalid rejection, exact and leftmost answers, the flat-payload execution
   story, valid-query adequacy/provenance, and physical/store refinement. Its
   proof at lines 154-186 explicitly supplies those conjuncts. The execution
   story definition at `RMQ/Core/SuccinctRMQClassic.lean:611-684` ties the
   physical words and successful-read backing to the canonical trace.

2. **Controller boundary: PASS.**
   The construction theorem comment at
   `RMQ/Core/SuccinctFinalRAM.lean:9355-9364` expressly excludes controller
   operations and conventional word-RAM complexity. The same boundary is
   stated in `docs/TRUST_AUDIT_PACKET.md:87-96`,
   `docs/WORD_RAM_REVIEW_PACKET.md:92-104`, and the other canonical paper
   documents. Charged events are reads and word rank/select primitives; input
   and register access, dispatch, arithmetic, tests, branches, decoding, local
   scans, candidate merges, trace assembly, and the validity guard remain
   outside the charged model.

3. **Historical role quarantine: PASS.**
   The detailed `118`, `328`, `4144`, `196727`, `Ready`, zero-block,
   route-split, and `2^128` chronology is explicitly classified as
   compatibility or proof-only material in
   `docs/digests/SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md:1-69`.
   The few route-split/zero-block mentions in the current packets occur under
   explicit compatibility boundaries. Formal Ready/zero-block identifiers in
   the family theorem inventory are theorem/proof inventory, not presented as
   the current execution route.

4. **Lifecycle language: FAIL.**
   No branch name, candidate status, worker status, or pending-audit claim was
   found in the named current Markdown documents. The canonical headline
   comments at `RMQ/Headlines/RMQ.lean:562` and `:612` nevertheless retain the
   worker-phase labels described in the second P2 finding.

5. **Paper import boundary: PASS.**
   `RMQPaper.lean:1` imports only `RMQ.Headlines.RMQ`. That canonical module's
   imports at `RMQ/Headlines/RMQ.lean:1-3` do not include compatibility.
   `RMQ.Headlines.RMQCompatibility` is introduced separately by the broad
   `RMQ/Headlines.lean` barrel.

6. **Changed relative Markdown links: PASS.**
   A focused diff parser checked all 22 added relative Markdown-link
   occurrences in `HEAD^..HEAD`; every resolved to an existing target.

7. **Topology lint file-set logic: PASS.**
   `scripts/paper_topology_lint.ps1:107-138` includes the current publication
   digest and other required paper surfaces in `$requiredFiles`.
   Lines 202-211 form the effective scan set from tracked files plus
   `$requiredFiles` plus `$MutationPath`, retaining existing untracked required
   files and virtual mutation targets before they enter `git ls-files`.

## Focused Verification

- Exact audit start: `git rev-parse HEAD` returned
  `95b5bc255475400c0f9d96c2b3a3f16de89bc128`; the audit worktree was clean.
- Theorem inspection: direct statement/body inspection of the canonical
  construction profile, `listIntSuccinctRMQPaperMainTheorem`, and their
  immediate execution-story dependencies.
- Focused `rg`: current lifecycle/phase vocabulary and historical
  cost/dispatch tokens over the named reader-facing surfaces.
- Relative-link check: 22 changed relative links, zero unresolved.
- Focused untracked-target topology check: while this report was still
  untracked, a virtual insertion of the retired public alias was rejected at
  this report path with `[removed-spelling]`; the mutation did not alter the
  file.
- `git diff --check`: pass after the report edit.

Per the audit instructions, `gate.ps1` and the full mutation suite were not
rerun. Exact-commit CI and artifact reproduction were accepted as already green;
the verdict rests on source and prose inspection, not those green results.

## Proof Digestion

Conceptually, the checked Lean result is coherent: one canonical payload, one
physical word representation, and one canonical global trace carry read
backing, exact answers, and the charged bound `76` together. The live caveat is
the explicit event-cost model: controller work is outside the charged trace.

The rejection is publication-topology only. A skeptical graduate student can
verify the theorem and still reasonably ask which current summary is
authoritative and why current canonical headline declarations use internal
phase labels. Until those two reader-facing ambiguities are removed, the
publication cleanup does not satisfy its own clean-reset contract.
