# E1 Architecture Finalization Coordinator Handoff

Prepared: 2026-07-23 America/Los_Angeles  
Purpose: self-contained, tool-neutral handoff to a Claude or alternative Codex coordinator  
Repository: `C:\Users\poin\Documents\RMQ`  
Accepted-governance checkout: `C:\Users\poin\.codex\visualizations\2026\07\17\019f6d85-7626-7433-a60b-81f8be29689a\b7r4-main-integration`

## Executive status

**No final E1 architecture has been selected. No B2, B3, B4, or A4 route
verdict has been accepted as a final architecture result. No architecture
integration, push, publication, public-claim synchronization, or E1 closure
occurred.**

The verified frontier is:

- Governance and local `main`: commit
  `a154983ae465b25ae6d8118b56abfa95ddf5b409`, tree
  `9232abdcacbda528a6294370476907237f4e98bb`, clean.
- B1 shared serializer/package prerequisite: accepted commit
  `1727de15f2030bfb9296a9b31508bc00581aa33a`, tree
  `8b7b2d508a03917dd2ea3f968c4d4d5f5431ef43`.
- PRELOGIC, PRECUR, and PREHIST reports: accepted local evidence inputs at
  commits named below.
- B3 historical source-port/interface prerequisite: accepted commit
  `c19061629ce8cf1e78992a99346170edd84b4971`, tree
  `bf10934b4034aaf3dade21a448dd246cf51e5c69`.
- B2 descriptor precondition: **not accepted**. R3 proved that the old frozen
  descriptor contract itself is false. This is a contract-repair result, not a
  proof that B1/Core is impossible.
- Full B3 historical route: **active and unaudited**, not terminal. Its branch
  has only the matrix-freeze commit; implementation files remain uncommitted.
- B4 total-`Nat` route and A4 selection: not launched and not accepted.

The immediate coordination objective is to preserve the active B3 checkpoint,
repair B2's validation-local contract, finish and independently audit all
route verdicts, and only then run A4.

## Hard startup gate for the next coordinator

Before substantive work, use a checkout containing the exact current
workflow-governance commit and run:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\project_skill_preflight.ps1 `
  -GovernanceRef a154983ae465b25ae6d8118b56abfa95ddf5b409 `
  -RequiredSkills rmq-coordinator `
  -RuntimeProjectSkills "<the RMQ skills actually exposed in that task>"
```

At handoff creation, the actual runtime RMQ catalog was:

```text
rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint
```

The preflight passed in the accepted-governance checkout with expected,
checkout, working, and runtime inventories all equal to those three skills.
Stop if the script is absent, governance is not in the checkout's ancestry,
the checkout skills are missing/stale, or `rmq-coordinator` is absent from the
actual runtime catalog. Do not substitute another skill and do not record
acceptance from a disclosed fallback.

Reconstruct the frontier from Git rather than from this prose:

```powershell
git status --short --branch
git log --oneline --decorate -20
git branch --all --contains HEAD
git worktree list --porcelain
git log --oneline --decorate --graph --all --simplify-by-decoration -35
```

Follow `docs/internal/AUDIT_PROTOCOL.md`. Worker prose, matrix statuses,
terminal transcripts, timings, and claimed verdicts are untrusted until
reconstructed from the exact committed tree.

## What the E1-ARCH research is trying to establish

E1 is the machine-model sibling of the M1 adequacy work. The research question
is whether the existing succinct RMQ construction can be executed by a small,
explicit, bounded-word machine on the **same counted physical object** used by
the space argument, with every relevant operation charged and every result
connected to the public half-open, leftmost-tie RMQ semantics.

The architecture investigation separated that question into:

1. **B1 shared physical object.** Construct one all-size counted image with
   descriptor, padded payload cells, sentinel, and dead cell; prove one
   query-independent logarithmic word width; expose uniform planner/executor
   interfaces; and give current, historical, and total-`Nat` routes
   definitionally identical inputs.
2. **B2 current route.** Lower the current E1/relative-RMM control path to a
   fixed bounded instruction semantics over the B1 image, including descriptor
   geometry, rank/select, LCA, fringe, trace, and cost-category accounting.
3. **B3 historical route.** Reconstruct the old fixed-topology 5,646-instruction
   program, port it without altering its semantics, and prove a bounded
   target run stutter-simulates it on the exact B1 package.
4. **B4 total-`Nat` route.** Decide whether the total-`Nat` certificate route
   supplies an independently lawful bounded route under the same object and
   guards.
5. **A4 selector.** Select only after every route has either a checked PASS or
   a quantifier-matched universal FAIL:

   ```text
   if current PASS then CURRENT_PRIMARY
   else if historical PASS then HISTORICAL
   else if total-Nat PASS then TOTAL_NAT_CERTIFICATE
   else NO_LAWFUL_FULL_WORD_ROUTE
   ```

An unresolved input stops A4. A timeout, an awkward encoding, a failed local
implementation, or a theorem about a proxy is not a universal route FAIL.

### What has been hardened so far

The work deliberately added evidence barriers against several common
false-positive patterns:

- frozen requirement matrices with stable IDs and raw-Git UTF-8 chronology;
- exact two-commit freeze/implementation histories and closed path scopes;
- same-object identities from source values through serializer, image, route
  input, run, trace, and output;
- checked expected-type consumers that must fail if a mandatory proposition or
  object link is weakened;
- counterfactual mutation registries with explicit expected verdicts and exact
  failing surfaces;
- non-vacuous focused selectors, omitted/duplicate/unknown-ID controls,
  restoration, and terminal clean-state checks;
- evidence-based subprocess deadlines and process-tree termination;
- separation of payload bits, descriptor bits, fixed-cell reads, model
  instructions, ROM fetches, historical source counts, Lean runtime, and proof
  time;
- exact positive/negative predicate parity: a route FAIL must negate the same
  objects, guards, and quantifiers used by route PASS;
- rejection of semantic callbacks, host shape projections, expected-answer
  oracles, proof-supplied traces, decorative events, and disconnected opcode
  labels.

These controls have already rejected multiple superficially green candidates.
They are part of the research result: the architecture evidence is stronger
because claims are forced through executable and mutation-sensitive consumers.

## Architecture DAG and accepted inputs

```text
governance a154983
        |
        +--> accepted B1 1727de1 --------------------+
        |                                             |
        +--> PRELOGIC d3a2354 --> B2 current route ---+---+
        +--> PRECUR   5173171 --> B2 descriptor ------+   |
        |                                                 +--> B4 total-Nat
        +--> PREHIST  50c5f8c --> B3 source port ----------+      route verdict
                                      |                    |
                                      v                    |
                              B3 full historical route ----+---+
                                                               |
                   accepted B2 + accepted B3 + accepted B4 ----+--> A4
                                                                    |
                                                                    v
                                                     integration/public sync
```

Accepted inputs:

| Input | Commit | Tree / key blob | Meaning |
|---|---|---|---|
| Governance/local main | `a154983ae465b25ae6d8118b56abfa95ddf5b409` | tree `9232abdcacbda528a6294370476907237f4e98bb` | Current workflow and merged frontier |
| B1 | `1727de15f2030bfb9296a9b31508bc00581aa33a` | tree `8b7b2d508a03917dd2ea3f968c4d4d5f5431ef43`; Lean blob `d998129cb4f796ef1fd82ae7bc3c80735dbbef18`; matrix blob `9eb1625a6023eb36bd2ceefdcc44396eb768f3c6` | One checked all-size shared serializer package and identical route-input aliases; no route execution |
| PRELOGIC | `d3a23540b124e8c7b9a5306d5c616954372e56d2` | tree `f181f157a31256cd1786a89a3aa49675f5606b53`; report blob `086abee6279cb0fa8ed01975abc5cdbd4e0dfb27` | Predicate implications, selector assignments, B4 classification, DAG |
| PRECUR | `517317117c07858ebd8be6f71bc8c73ef353c935` | tree `4d93d89b2a1d75091405c05d3b4978f35b91e765`; report blob `22a41fc691e948e3a609f95e80867490b432aba1` | Current-route atomic lowering, reads, composites, literals, widths, traces |
| PREHIST | `50c5f8ccf7be83a56b90a6c29142ac32860f0a27` | tree `c873a3d637855009cac8e4bda9c9a0e7f1964959`; report blob `be80468ef049c0c94c7d1a7b3c5f8f69ccfd453f` | Historical ISA, encoder/interpreter, literals, widths, simulation obligations |
| B3 source port | `c19061629ce8cf1e78992a99346170edd84b4971` | tree `bf10934b4034aaf3dade21a448dd246cf51e5c69`; matrix blob `4f8b3c84fbac5d8ef766b5d3df1c289c097fbeb3`; runner blob `6939ebe699776e420c799a9e1aaba4d560028c00` | Accepted validation-local 56-module, 5,646-instruction, twelve-constructor source interface |

B1's accepted proposition is a prerequisite, not the architecture verdict. It
constructs the exact package, fixed cells, width/image facts, executor, and
forty-seven-field consumer, and it exposes `currentE1SharedRouteInput`,
`historicalE1SharedRouteInput`, and `totalNatE1SharedRouteInput` as the same
package. It does not supply any bounded route run or receipt.

## B2 chronological disposition

### R1: rejected proxy obstruction

- Branch: `codex/e1-arch2-b2-descriptor-closure-r1`
- Freeze: `500a757b01de550ad49ee602a946a75202799c09`
- Candidate: `83d9b1223bb018e5889b693400d39e955a1438a7`
- Candidate tree: `9889a56752b808e5a97b7e1e5283847ecbc42a9b`
- Freeze matrix blob: `2b9178bd5efb77a39405a66d24324c696933f994`
- Final matrix blob: `0703d9b6b4ee2ab0ca9e671e1119aed72e98c8fc`

R1 passed much structural checking, but its OBSTRUCTED claim was invalid.
`directSemanticForGlobalLevelCount := none`, a false direct-opcode flag, and a
hand-authored repair registry do not negate the frozen target and do not prove
target-to-`False`. Its replay also had a fixed two-second
descendant-sleeper/PID-receipt race. Treat R1 only as immutable negative
evidence for proxy obstruction and deadline design.

### R2: rejected disconnected executable surface

- Branch: `codex/e1-arch2-b2-descriptor-closure-r2`
- Freeze: `f62cdc8b8fb1425c8b032c30cb5ac197035c1f6c`
- Candidate: `b2d8b1a756927cd2566b4373826e774846507b5f`
- Candidate tree: `9a7ac943428c283e2e027fd5ebd25ac5b5cc06f3`
- Freeze matrix blob: `1408caa7a6b304d3e372f097eed4003d6b662570`
- Final matrix blob: `062c802d854f11f20331ab8b13820710363c1620`
- Closure blob: `1289301b7363ca555e1d66f806dd27919efcf121`
- Fixtures blob: `390a85cd1cf6194a23d686738033f034d90cb637`
- Replay blob: `ad697a04f2beaef47af44fe9caa7a6d668dea92f`

R2's old expected-accept replay passed, but the central claim was
disconnected. `segmentEndRecoveryProgram` and
`levelChunkRecoveryProgram` were opcode-tag lists without operand-bearing
instructions, machine state, evaluator, step/run relation, or a theorem
connecting execution to the recovery functions. The typed consumer pinned
only list lengths. G25 also used host `shape.size` rather than the charged
`loadedNat` at `sharedSizeAddress`. R2 is an immutable negative fixture for
disconnected opcode lists, uncharged projections, and weak consumers.

### R3: valid refutation of the old contract, not B1/Core obstruction

- Branch: `codex/e1-arch2-b2-descriptor-closure-r3`
- Base: `1e111e574c9593a6eb77d9e482d8a913fa4d7e91`
- Freeze: `1f2003645a2014688f1ff11b5dca2c7ddbe99ef1`
- Freeze tree: `cf98865afb5530494712f8c2124f842db745f323`
- Freeze matrix blob: `a15b723f5762a33b91370dc9b015e4fa2bc21e6a`
- Candidate: `250fba1685411089825cbb8245a4fc3180678e77`
- Candidate tree: `92f5fd5a65d58faa61ab0089d32814c630af7d93`
- Final matrix blob: `12eafa12e6e8905d322f3ece7b8a1f5fe2251829`
- Closure blob: `58323facefc44cc49038f092c30ac86c2d3f21c4`
- Fixtures blob: `e9a65c1b432d425d32fb21db55aa073a14c722ac`
- Worktree: `C:\Users\poin\.codex\worktrees\b1cf\RMQ`, clean when this
  dossier was created.

R3 soundly proves:

```lean
def FrozenG10LongBlocksPerSuperClause : Prop := ...

theorem frozenG10LongBlocksPerSuperClause_false :
  Not FrozenG10LongBlocksPerSuperClause

theorem frozenCompleteDescriptorPrecondition_obstruction
    (hG10 : FrozenG10LongBlocksPerSuperClause) : False
```

The size-50 witness yields current
`longFlagRankData.blocksPerSuper = 1` while the old frozen G10 clause demands
equality with rank word width `2`.

This does **not** prove that B1 or Core is impossible. It proves the validation
contract copied the wrong geometry:

- accepted current long and sparse definitions use `blocksPerSuper = 1`;
- old G10 substituted rank word width for that current field;
- old G06 used `blockCount := N / blockSize`, while accepted current geometry
  uses `N / base`, equivalently `bpCode.length / blockSize`;
- old G14 universally equated segment-19 and segment-0 word lengths, but the
  empty shared-store case has a sentinel-bearing physical rank-store
  distinction.

Therefore R3's `OBSTRUCTED` applies to the obsolete frozen conjunction. The
next B2 action is a **governed validation-local contract correction plus real
executable descriptor closure**, not an automatic B1/Core rewrite.

### B2 R4 prompt artifact

`C:\Users\poin\.codex\visualizations\2026\07\17\019f6d85-7626-7433-a60b-81f8be29689a\E1_ARCH2_B2DESC_R4_PROMPT.md`

- Status: **DRAFT / NOT LAUNCHED**
- Size: `18,623` bytes
- SHA-256:
  `A3EC3C3077FEE9A34D34FBD745D393ED2DF9BAB92DA081CFDB79F5F6091A47CF`

Before any use, re-read it against then-current governance and source,
reconstruct R3 independently, run `worker_prompt_preflight.ps1`, and keep it
non-launchable until the reusable failure-mode feedback is complete. Correct
its base/dependencies if B3 or governance has advanced. It is a prompt
artifact, not evidence and not authority to launch.

## B3 historical route status

### Accepted source-port prerequisite

The accepted source-port chain is:

- base `1e111e574c9593a6eb77d9e482d8a913fa4d7e91`;
- freeze `5f8f08091dbe0399c64942c3192b524c3b6e121c`, tree
  `75ccbbfa9074ab7357d23c1d6b2e775d685fa167`, freeze matrix blob
  `2de01e1f69857b8ae86cc96d60b22c00bea9724c`;
- implementation `c19061629ce8cf1e78992a99346170edd84b4971`,
  tree `bf10934b4034aaf3dade21a448dd246cf51e5c69`.

It supplies the validation-local ordered 56-module port, 5,646-instruction
closed program, twelve-constructor interface, source PCs 1/5/7, exact pinned
fixture, and a terminal twelve-case replay whose history parser splits exactly
two ordered commit hashes. This is accepted as a source/interface
precondition only; it is not a bounded B3 route.

### Full B3 route: active, not audited

- Task: `019f91b4-c2ea-7d83-828b-5b43b7aae15e`
- Branch: `codex/e1-arch2-b3-historical-route-r1`
- Worktree: `C:\Users\poin\.codex\worktrees\bb61\RMQ`
- Exact base: `c19061629ce8cf1e78992a99346170edd84b4971`
- Only committed child: freeze
  `0554c0f7ad031f43c99aa3b4457fc5168268abb4`, tree
  `903c00b4458751d6dc4ec3c7ca39ea6c962f6e1`, parent
  `c19061629ce8cf1e78992a99346170edd84b4971`
- Freeze matrix blob:
  `f292cd75b48d56312bacb7d33a7ff7e463f6b650`
- Frozen prompt SHA-256:
  `EF0112772907E0005BF5B6A978EF7903957CFA0DEF948CF1FABB3F064165D320`
  (`22,058` bytes)
- Compact task status at dossier creation: thread `active`; latest turn
  `inProgress`.

The worktree was deliberately **not clean**: the two decision logs were
modified, and `RMQ/Validation/E1Architecture/B3HistoricalRoute/` plus
`scripts/e1_arch2_b3_historical_route_replay.ps1` were untracked. No
implementation commit, final tree, terminal replay, or coordinator audit
exists.

The active worker reported progress toward a fixed 5,646-entry semantic ROM,
canonical four-cell encoding, charged arithmetic, explicit physical-read
traces, run-derived events/receipts, a shape-independent topology theorem, and
a fail-closed replay skeleton. The latest reported open integration issue was
connecting fixed-cursor recipe lowering, including multiplication/division
phases, to the actual recursive bounded target run without a proof-premise
bypass. These are **unverified worker checkpoint statements**, included only
to help a successor recover the research intent. They are not accepted facts.

The successor coordinator must either let the existing user-owned task finish
or explicitly preserve and inspect its working checkpoint. Do not launch a
duplicate. When terminal, audit the exact final two-commit candidate against
the frozen prompt and `AUDIT_PROTOCOL.md`, including:

- proof-free inhabited route domain;
- one fixed semantic ROM and canonical codec;
- total source-PC lowering and charged immediate derivation;
- explicit bounded microsteps for all twelve constructors;
- physical descriptor/payload/sentinel/dead reads;
- reachable width, address, capacity, and no-wrap invariants;
- one actual run-derived receipt;
- phase-indexed source stuttering simulation;
- position/multiplicity-sensitive trace projection and category/fetch counts;
- all-shape/all-representable-query `ParameterizedComplete`;
- pinned receipt from the same constructor;
- exact `P`, `Q`, `HistoricalPASS`, `HistoricalFAIL`, and iff parity;
- independent expected-type consumers;
- full ordered mutation registry, selectors, deadlines, tree kill,
  restoration, clean state, and one terminal committed replay.

Until that audit succeeds, B3 is `ACTIVE/UNVERIFIED`, not PASS, FAIL, accepted,
or obstructed.

## Remaining work to finalize architecture

1. **Preserve and finish/audit B3.** Do not discard or overwrite the active
   worktree. If it terminates incomplete, classify the exact gap as local
   implementation, reusable workflow failure, or genuine architecture choice.
2. **Repair B2's contract locally.** Re-freeze G06, G10/G12, and G14 against
   exact accepted current definitions; then implement operand-bearing
   instructions, state, evaluator, run relation, charged B1 initialization,
   G24/G25 semantic correspondence, trace/count facts, and typed consumers.
3. **Run full B2 current-route work** only after the descriptor prerequisite is
   independently accepted. The full route still owes the exact B1 object,
   bounded run, result, trace, footprint, logical projection, ROM fetches,
   categories, and all-size proof.
4. **Decide B4 total-`Nat`.** Use the exact PRELOGIC predicate and the same B1
   object. A local implication or unreachable-arm observation is not a verdict;
   produce a concrete PASS or exact universal FAIL.
5. **Run A4 only when B2, B3, and B4 are each independently accepted.** Every
   input must carry a checked positive witness or a quantifier-matched negative
   theorem. Apply the frozen priority order; unresolved means stop.
6. **Integrate only with explicit user authority.** Reconstruct ancestry,
   non-owned identity, design logs, public theorem dependencies, and required
   blind exact-commit audits before any merge.
7. **Synchronize public claims after selection.** Derive the closed inventory
   from `docs/internal/CLAIM_DRIFT_POLICY.json`
   `currentFactSurfacePathRegex`; update theorem maps, README/paper/artifact
   claims, and digestion records only to the accepted result.
8. **Deferred B1 provenance wording.** In
   `docs/internal/E1_FINAL_ARCHITECTURE_ADJUDICATION.md`, correct P2-1 so
   operational facts are sourced from the actual terminal command receipt,
   while Git history establishes commit/tree/blob identity and chronology.
   Preserve the accepted B1 proof, matrix, verdict, and every other claim.

## Numbered next-coordinator runbook

1. Run the project-skill preflight at the then-current accepted governance.
2. Reconstruct `main`, all named commits, worktrees, branches, active tasks, and
   automations. Check the exact handle/base/branch tuple before creating
   anything.
3. Inspect the active B3 task. If active, do not steer or duplicate it. If
   terminal, freeze its exact reported HEAD and audit it independently.
4. For B3, require exactly two commits after `c190616...`, correct parents,
   owned paths only, non-owned blob identity, and terminal clean state. Reject
   a dirty checkpoint or a third commit.
5. Reconstruct B3 theorem shapes and expand definitions. Counterfactually test
   expected-type consumers, actual-run provenance, and exact `P`/`Q` parity.
6. Run focused B3 Lean roots and exactly one final full committed replay only
   after cheap structural/selector checks pass. Never repeat an unchanged
   expensive stage after timeout.
7. Record B3 as ACCEPTED, exact repair-needed, or genuine OBSTRUCTED. A genuine
   obstruction must prove the frozen target false over identical objects and
   quantifiers.
8. Re-read and semantically review the B2 R4 draft. Correct its contract,
   generate a fresh governed base if needed, and run prompt preflight. Do not
   launch it merely because the artifact exists.
9. Complete the reusable feedback loop for B2: R1 proxy obstruction, R2
   disconnected programs/host projection, and R3 stale contract must be named
   regressions that the new replay rejects.
10. Audit the eventual B2 descriptor candidate, then separately launch/audit a
    full current-route worker. Do not call descriptor closure full B2.
11. Prepare and audit B4 only after its exact dependencies are available.
12. Apply A4 only when all three route verdicts are accepted. If any is
    unresolved, stop without choosing an architecture.
13. Obtain explicit user authority before merge, push, public synchronization,
    branch deletion, worktree cleanup, or E1 closure.
14. After authorized integration, run proportional final verification and a
    fresh blind whole-frontier/public-capstone audit before publication.

### Stop conditions

Stop for user/coordinator architecture judgment if a checked theorem shows that
the unchanged allowed route model requires a new primitive, different
atomicity/cost model, Core edit, B1 interface change, or incompatible public
claim. Stop for workflow repair if governance/preflight fails. Stop rather than
launch around an active duplicate, dirty ambiguous worktree, missing exact Git
object, weakened quantifier, non-green terminal replay, or public-surface scope
expansion.

## Known failure modes and named regressions

| Failure mode | Exact lesson |
|---|---|
| Proxy obstruction | Absence of a direct opcode/registry entry does not negate an allowed construction. Require exact target negation or target-to-`False`. |
| Disconnected opcode lists | Tags and list lengths are not an executable program. Require operands, state, evaluator, step/run, final-state equality, and a consumer pinning all of them. |
| Uncharged shape projection | `shape.size`, host `Nat.log2`, or sibling semantic data cannot supply a charged runtime operand. Use exact B1 loaded cells and executed derivations. |
| Two-second sleeper race | A fixed short deadline can race PID receipt and create a false negative. Use measured deadlines of at least ten seconds and prove root plus descendants are gone. |
| Joined `rev-list` hashes | PowerShell can preserve two lines as one object name. Materialize, split, and validate exactly two ordered, distinct 40-hex commits before any object spec. |
| Weak expected-type consumer | Pinning names or lengths permits proposition/object bypass. The independent consumer must mention the full public proposition and exact composition chain. |
| Frozen-contract drift | A formal obstruction to a stale clause is not an obstruction to current Core/B1. Compare the frozen row to exact current definitions before interpreting the result. |
| Decorative trace/category fields | Hand-authored or proof-supplied logs can look execution-backed. Observations must be structural outputs of the actual recursive run. |
| Monolithic definitional reduction | A 5,646-entry equality can hit resource limits without semantic mismatch. Decompose through the builder graph; do not call resource exhaustion obstruction. |
| Replay extractor/path defects | Case-insensitive Windows path collisions and broad row extractors can make harnesses unsound. Self-test failure-closed registry and path handling. |
| Active B3 bridge risk | A standalone recipe evaluator is not the bounded target. Multiplication/division and literal derivation must be observed phases of the same target `step`/`run`, not proof premises. |

## Compact artifact index

All prompt paths below are under:
`C:\Users\poin\.codex\visualizations\2026\07\17\019f6d85-7626-7433-a60b-81f8be29689a`

| Artifact | Identity | Classification |
|---|---|---|
| This dossier | `E1_ARCHITECTURE_COORDINATOR_HANDOFF.md` | Editable handoff, not proof evidence |
| B1 adjudication | commit `1727de...`; doc blob `32313920d5b13bfe968606430636e31372560b19` | Accepted prerequisite evidence |
| B1 acceptance matrix | blob `9eb1625a6023eb36bd2ceefdcc44396eb768f3c6` | Immutable accepted contract input |
| PRELOGIC report | commit `d3a235...`; blob `086abee6279cb0fa8ed01975abc5cdbd4e0dfb27` | Accepted local report |
| PRECUR report | commit `517317...`; blob `22a41fc691e948e3a609f95e80867490b432aba1` | Accepted local report |
| PREHIST report | commit `50c5f8...`; blob `be80468ef049c0c94c7d1a7b3c5f8f69ccfd453f` | Accepted local report |
| B2 R1 prompt | `E1_ARCH2_B2DESC_R1_PROMPT.md`; 12,623 bytes; SHA-256 `BE461480A0A9CD60C71EC17DFB1BB9D6185DF44B64E100C1F3931339A5347213` | Historical prompt artifact |
| B2 R2 prompt | `E1_ARCH2_B2DESC_R2_PROMPT.md`; 15,832 bytes; SHA-256 `40F8842FD00D67199DCA6FF9FD4D7C01FD20C7F277565ED84C552DDF8B8F3736` | Historical prompt artifact |
| B2 R3 prompt | `E1_ARCH2_B2DESC_R3_PROMPT.md`; 14,838 bytes; SHA-256 `ABC0EF76B4FF4FE2EEAA7407CFA74F4F9860E431C6DFD4CB4575DD558F08FAD7` | Historical prompt artifact |
| B2 R4 prompt | `E1_ARCH2_B2DESC_R4_PROMPT.md`; 18,623 bytes; SHA-256 `A3EC3C3077FEE9A34D34FBD745D393ED2DF9BAB92DA081CFDB79F5F6091A47CF` | **DRAFT / NOT LAUNCHED** |
| B3 source-port R2 prompt | `E1_ARCH2_B3PORT_R2_PROMPT.md`; 12,566 bytes; SHA-256 `1CDBBE6B47AC8E3C36C67B73F04616C25757C25B69E59708F540E5F37799742B` | Historical prompt; accepted output is `c190616...` |
| B3 full-route prompt | `E1_ARCH2_B3ROUTE_R1_PROMPT.md`; 22,058 bytes; SHA-256 `EF0112772907E0005BF5B6A978EF7903957CFA0DEF948CF1FABB3F064165D320` | Frozen active-task contract |
| B3 active task | task `019f91b4-c2ea-7d83-828b-5b43b7aae15e`; branch/worktree above | Active, dirty, unverified checkpoint |

Every named commit and blob was resolved with Git while preparing this dossier.
Prompt hashes and byte sizes were recomputed from disk.

## Final handoff checklist

- [ ] Preflight current governance with the actual runtime RMQ catalog.
- [ ] Confirm `main`, governance, and accepted inputs have not advanced.
- [ ] Preserve the active B3 task/worktree; do not duplicate or overwrite it.
- [ ] Audit B3 only after terminal status and a clean exact two-commit candidate.
- [ ] Treat B3 checkpoint prose and uncommitted files as unverified.
- [ ] Re-freeze B2 against current definitions; do not edit B1/Core by default.
- [ ] Keep B2 descriptor acceptance separate from full B2 route acceptance.
- [ ] Produce and independently audit a B4 PASS or exact FAIL.
- [ ] Do not apply A4 while any route is unresolved.
- [ ] Obtain explicit authority before integration, push, cleanup, publication,
      or closure.
- [ ] Run fresh blind capstone audit before public synchronization.
- [ ] Correct deferred B1 provenance wording without changing its proof/verdict.

## Explicit uncertainties

1. The active B3 work may finish successfully, expose a local repair, or reveal
   a genuine primitive/atomicity/cost-model choice. No terminal disposition was
   available when this dossier was frozen.
2. The B2 R4 prompt has not been semantically revalidated after the live B3
   checkpoint and is not launch-ready merely from its current hash.
3. B4 has no accepted route verdict, so A4 cannot yet distinguish the final
   fallback case.
4. Public claim surfaces have not been inventoried against a selected
   architecture because no selection exists.
5. This dossier records repository and process evidence. It does not replace
   kernel theorems, committed replays, or a fresh blind exact-commit audit.

