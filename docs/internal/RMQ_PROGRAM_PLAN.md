# RMQ program plan v15

**Date:** 2026-08-16.
**Verified at:** `17360d1`, an ancestor of `codex/rc3-corrections`. Every SHA
cited as a **landing** below is an ancestor of that tip, checked. One SHA
deliberately is not: `648e512`, the tip of
`claude/b1-b2-charged-fringe-tables`, which §E cites and §0 identifies as the
tip of a separate branch.
Two further SHAs, `543de42` and `b53c08d`, are orphans of a history rewrite —
`git branch --contains` is empty for each — and are cited only here;
their surviving counterparts are `acfb7ef` and `b0b83b9`.

**"At this pin" means the repository state at that commit.** It does NOT mean the
commit containing this file: a revision cannot name the commit that introduces
it, because writing the SHA in changes it. Claims about artifacts committed
*with* this revision say so explicitly and are true of that later commit, not of
the pin -- the distinction exists because a previous revision collapsed the two
and ended up speaking from two commits at once.

**Supersedes v14.** Defect-species record: `PLAN_LINEAGE.md`, which carries
no per-revision attribution table, deliberately.

## Method

Revision-history commentary belongs in `PLAN_LINEAGE.md`, not here. One reason is
an account of what audits of this plan found — **UNVERIFIABLE**, because
those audits have no committed record (§K): they found the revision-history layer
carrying the great majority of this plan's defects, while its technical content —
§C.1's arithmetic, §C.2's obligation fidelity, §A's finding fidelity, and the
repository line citations checked in the final round — verified exact. Not
*every* such citation: §J item 6 lists repository pointers that audits found
stale, and `PLAN_LINEAGE.md` species 6 records a stale `gate.ps1` pin. That is
why §J item 6 exists, and why no count is given for it either. The structural reason does not depend
on that account: a wrong obligation is wrong once, but a wrong claim about a past
revision breeds a correction that is itself a claim about a revision.

Claims about past revisions still appear below and are removed as they are found.
**No count is given** — a tally beside the list it tracks is the defect species at
`PLAN_LINEAGE.md` species 3, and one stated here would need maintaining every
revision. The rule is that no new claim about a past revision is added **except where a
claim already present is found wrong and correcting it requires naming its
object** — §A.2b carries two such corrections and §C a third (the `best`-field
truncation, broadened from v5 to v4 and v5 on measurement), and each states what
was measured. An unforced claim about a past revision is the thing being removed; a
retraction is not one. What belongs here is what is to be done, and what is true
of the repository at the pin.

§A is the coverage map: every accepted finding, DD entry, non-goal and contract
obligation, each mapped to a section or explicitly marked not-carried with a
reason. **A finding may be dropped; it may not be dropped silently.** **Any
future revision must reproduce §A in full before changing anything else.**

§A.3 and §A.4 still point at §D and §B rather than enumerating their items. A
pointer cannot show a drop, so that is a real weakness and it is **open**, not
fixed.

---

## A. Coverage table (the load-bearing section)

### A.1 Plan-audit findings — `PLAN_AUDIT_DISPOSITION.md`, 14 accepted

| id | requirement | carried in |
|---|---|---|
| `P0-1` | Contract-first; acceptance test is that the auditor's fake and stronger ones are excluded by a **named** obligation | §C, §D |
| `P1-1` | DD-A stays conditional on the capstone-seam feasibility probe | §B DD-A |
| `P1-2` | All-row adjudication over the 11 REQ rows, inherited INV rows, CHK rows, `REQ-E1-09`, `L-OPEN-06`, the evidence matrix **and every current-fact surface**, disposed atomically | §E |
| `P1-3` | Retired narrative stays retired: "two independent operational refinements connected to the same public RMQ semantics"; "one protocol" only after a checked join theorem reconciled with `independence_check` | §E |
| `P1-4` | E1 stays strictly supplementary **or** its public landing is a new release candidate requiring the full release audit; **owner decision, in the DD packet** | §B **DD-C** |
| `P1-5` | Shape lane respecified as persistent monotone-stack scan or direct shape emitter, **with value agreement against the canonical shape proved**; charging the existing builder **prohibited** | §D non-goal 11 |
| `P1-6` | Roadmap staleness escalated to the roadmap. **The inventory is derived from `CLAIM_DRIFT_POLICY.json` at the pinned commit with a per-path disposition; no fixed count is pinned anywhere** | §F |
| `P1-7` | Predicate requires signed-word representability of every input and compared operand at the declared width, with a comparison/order refinement theorem and an exhibited satisfiable all-size family. **Absent that, the model is called a unit-cost comparison oracle in public wording** | §C obligation O-REPR |
| `P1-8` | New root checks import **only** that root, with exact declaration inventory, count floor, deletion mutation, anti-empty control. **Frozen executable name preserved; alias may be added, never a rename.** Packet manifest and operational-surface list enumerated, not counted | §E, §D non-goals |
| `P2-1` | One committed script emits separately named fields — root-inclusive files, imported dependencies, physical lines, non-blank lines — with wrapper, off-by-one and blank-line mutation controls. **No percentage quoted without its unit** | §F, scheduled §H item 6 |
| `P2-2` | "One shared payload sub-builder"; physical-store emission separately costed; **write units stated** | §C |
| `P2-3` | Report **five wrappers / eight encoded tables**; `2n` forecast removed until DD-E | §B DD-E, §C |
| `P2-4` | Session figures are planning hypotheses, **relabelled not deleted**; E1 gate uses the upper estimate plus audit buffer; calendar gates update only from an official 2027 CFP | §G |
| `P3-1` | "Zero proof obligations" → "neither discharges the other"; "zero-paper-facing" → **"no positive paper claim"**; **`M1 → S1` retained as a deferred non-gating edge**; both roadmaps and the packet manifest synchronized — **the packet ships the stale DAG** | §E (wording), §H item 7 (sync) |

### A.2 RC-3 candidate findings — `RC3_DISPOSITION.md`, 10 accepted

`RC3_DISPOSITION.md:12` says "Eleven findings: three `P1`, six `P2`, one `P3`",
which is ten. Its §3 enumerates ten. The ten are used here; the source's own
total is wrong and is not carried.

All landed at the pinned commit **except two**: `P2-5` (open, §B `DD-H`) and
`P1-3` (partial — the deadline was re-derived, but its disposition's
tail, "then the entire aggregate is rerun from a clean exact checkout", is not
done; §H item 3).
v5 pointed at a landing table in §H; §H is a to-do list and no such table
existed, so §A.2's whole "landed" column rested on nothing the plan showed.

**Labels.** An earlier revision mislabelled six of the ten and dropped `P2-6`
outright while asserting it closed. The titles below are `RC3_DISPOSITION.md`
§3's own, verified against it and, **at this pin**, against the repository's
independent attributions: in `scripts/gate.ps1`, the comment naming `P1-2` sits
beside the EG-CP replay calls, and the comment naming `P2-3` sits beside the
axiom whitelist. Both are checked at this pin.

**Citations into `scripts/gate.ps1` are given by content, not by line.** That
file is edited in most rounds, and a line pointer into it went stale twice in
two commits — `PLAN_LINEAGE.md` species 6, the species named for exactly this.
A content anchor (`grep` for the quoted text) survives any edit that does not
remove the thing being cited, which is the only edit that should invalidate the
claim.

One of these pointers has moved already: the round-4 commit grew the
axiom-whitelist block by 16 lines and shifted everything below it, so a
citation into the lower part of `gate.ps1` is correct at one pin and wrong at
the next, while `:54`/`:55` survive because the growth sits beneath them.
That is §J item 6, learned from experience rather than asserted as principle.

| RC-3 finding | landed as |
|---|---|
| `P1-1` the manuscript is not the release-candidate manuscript (`RC-10` FAIL) | `0665b49`, `ffe8d3e` |
| `P1-2` the required aggregate omits both architecture replays | the two `Invoke-Checker` calls in `scripts/gate.ps1` for `eg_cp_stagea_replay.ps1` and `eg_cp_final_falsification_replay.ps1`, both hard — neither carries `-Soft` |
| `P1-3` the required full aggregate exceeded its own topology deadlines | `scripts/paper_topology_lint.ps1:12,21` (300 → 900) — **tail not done, §H item 3** |
| `P2-1` the independence checker watches the wrong terminal theorem | `scripts/independence_check.lean:84-88`, all three |
| `P2-2` three advertised checkers have direct false-success inputs | `4549cb2`, hardened `b0b83b9`; the two remaining classes closed `WDD-20260818-081`. **An outside plan audit on 2026-08-19 found this row asserting a closure that had not happened**: the disposition required all three exact classes to become persistent self-tests, and two never did -- `check_paper` still accepted `a fixed number of word-RAM steps`, `claim_drift -Strict` still accepted `executes in 210 word-RAM instructions`, and no `.ps1` in the repository held either probe string. Reproduced at `27c5641` and fixed. **Two scope caveats.** (i) WDD-20260816-042 records the conflict scan as **shape-limited by construction** — "no shape-based detector can close it" — and records that WDD-035's injection verification could not match its own shape. (ii) A second, concrete false-success input was live until `d31064c`: `$historicalMarker` contained bare `was`, so ``constant `214` was adopted`` — a conflict **inside** the declared shape — exited 0. That is `P2-2`'s own subject, undischarged at `b0b83b9` |
| `P2-3` trust and headline gates check a curated subset | yes. The axiom whitelist landed (`$allowed = @('propext', 'Classical.choice', 'Quot.sound')` in `scripts/gate.ps1`); round 4 (`d31064c`, WDD-20260816-043) widened its parse from 36 of 104 records to 104 of 104, after finding that Lean wraps long dependency lists and 68 records were never read. The disposition also requires "independent expected-type consumers for the standalone lower-bound, List-Int, readWord **and** packed aliases" — four. Only the packed one existed (`51a0a43`) until `15865e1`, where the other three landed (DD-20260816-117) and are present at the pin, each verified to fail closed by a mutant that stops the file elaborating |
| `P2-4` the strict claim scan breaks the fresh-blind boundary | `c04c101` |
| `P2-5` only the Windows ownership implementation was exercised | **NOT DISCHARGED** — probe only (`790f20b`); §I |
| `P2-6` the lower-bound load-bearing counterfactual is not persistent | `9699439` — `query_ne_none`, `null_decoder_impossible`, `wrong_answer_impossible` in `scripts/headline_axiom_check.lean`. **Scope caveat:** DD-20260816-112 records that these constrain `ExactRMQShapeEncoding.query_exact`, while the cited lower bound quantifies over `ExactRMQStateEncoding`; they reach it only through `exactRMQShapeEncoding_of_stateEncoding`. Retargeting is open work |
| `P3-1` stale paper evidence metadata | `docs/PAPER_CLAIM_CORRESPONDENCE.md:115` now `:498`; matrix counts corrected; the `file:line` citation checker landed (`3b920f7`, hardened `b0b83b9`) |

| id | landed | note |
|---|---|---|
| `P1-1` `P1-2` | yes | |
| `P1-3` | **partial** | deadline re-derived; its tail — rerun the aggregate from a clean exact checkout — is not done; §H item 3 |
| `P2-1` `P2-2` `P2-4` `P2-6` | yes | `P2-2` and `P2-6` carry scope caveats above |
| `P2-3` | yes | the three missing expected-type consumers landed at `15865e1`; mutation-checked |
| `P2-5` | **NO** | POSIX `setsid` containment; §B DD-H |
| `P3-1` | yes | **stale paper evidence metadata** — the `:490`→`:498` pointer and the matrix counts. v5's row carried the tag-annotation text instead, which is a different accepted item (`RC3_DISPOSITION` §5 item 11), so one item was displaced by another and neither was checked |
| §5 item 11 | yes | tag annotations carry identity and scope only (`b620e15`) |

### A.2b Contract obligations — the class where the drops happen

`wf3_attack.json` `required_repairs` holds 13 repairs. The plan adopts contract
B, so the `[A]`-only repairs `R4`, `R6`, `R7`, `R8` and `R9` are correctly out of
scope. `R5` is `[A]`-tagged too but IS in scope: contract B carries its property
as `REQ-BLD-13`, which is why `FK-2` does not survive B.

**A standing lesson, kept here because it is a method rule and not history.**

An earlier revision of this plan accused two of its predecessors of truncating a
quotation to manufacture an error. The accusation was false, and it entered the
document by a specific route: an audit reported it, the report was checked by
confirming the quoted text existed — and the check stopped there. Nobody counted
the underlying tags. Counting them settles it: **six** repairs carry an
`[A]`-only tag (`R4`, `R5`, `R6`, `R7`, `R8`, `R9`), so the disputed count was
genuinely wrong by one and nothing had been hidden.

**The quotation was verified and the arithmetic was not.** That extends §J item
2 — a claim is worth what was measured — to findings **received**, not only
repairs made. An auditor's conclusion is an input to be checked, not an output to
be adopted. Full account in `PLAN_LINEAGE.md`.

**It happened a second time, and was caught.** A later audit reported the claim
about v3 below contradicted, citing a sentence in v4. The citation is real and
says what the report said it says — but v4 was wrong about v3, and v3 was in the
same directory. That passage now states what v3 measurably contains.

**The citation was verified and the referent was not.** Same rule, one level
out: checking that a finding's evidence exists is not checking the finding.

The eight in-scope catalogue repairs and where each is carried (the five out-of-scope `[A]`-only repairs above are excluded):

| repair | carried as |
|---|---|
| `R1 [B, FATAL]` program uniformity | `O-UNIF` |
| `R2 [A AND B, FATAL]` reflected ISA + literal work cap | `O-WORKCAP` |
| `R3 [B]` no fittable padding parameter | `O-BITS` |
| `R5 [A, FATAL]` import firewall (B has it as `REQ-BLD-13`) | `O-FIREWALL` |
| `R10 [BOTH]` scratch memory | `O-SCRATCH` |
| `R11 [BOTH]` replay is not the anti-oracle | `O-REPLAY` + `O-NOINHERIT` + **`O-POINTWISE`** |
| `R12 [BOTH]` oracle negative control | `O-CONTROL` |
| `R13 [PROCESS, BOTH]` C1–C4 = `R1`,`R2`,`R5`,`R12` | §C.2b |

Plus three from the accepted findings rather than the catalogue: `O-REPR`
(`P1-7`), `O-WRITE` (`P2-2`), `O-COUNT` (`P2-3`). **Every obligation §C.2 defines
is named either in the table above or in the three lines just given** — checked
against §C.2, not remembered. No count is stated: a tally beside the list it
tracks is `PLAN_LINEAGE.md` species 3, and the obligation count is the instance
that file names.

v7 defined `O-POINTWISE` in §C.2 precisely to repair v6's drop of R11's fifth
locus, and did not add it to this table. The coverage table that exists to stop
silent drops dropped the obligation created to fix the previous silent drop.

**`R2` is the decisive one.** `FK-3`'s contract-B row — one of two `FK-3` rows —
ends "NEITHER CONTRACT HAS THE ROW
THAT KILLS THIS", and without it the cost half of the manuscript sentence is, in
the catalogue's words, "true-but-vacuous". `R2`'s content is `O-WORKCAP` — a
reflected ISA with a literal per-instruction work cap. **v3 shipped without it:
the string `R2` does not occur anywhere in its 196 lines.** v4 names `R2` once,
at `:197`, as a bare label after its inventory table rather than a row in it —
and asserts there that v3 "did carry" it, which v3 refutes. v5 restored the
label but keyed it to `O-SEG` — segment/counted-table identity — not to a work
cap.

### A.3 v2 non-goals — 10, all carried

Listed in §D.

### A.4 v2 DD packet — 6 entries

Carried in §B with **v2's identifiers preserved**.

---

## B. Owner-decision packet

Identifiers are v2's. New entries take fresh letters; none is ever reassigned.

| id | decision | status |
|---|---|---|
| `DD-A` | Retire the minimal-root goal | Open — **conditional on the capstone-seam feasibility probe**, which has not run. May not record "minimization exhausted" before it does |
| `DD-B` | Spoke claims: manuscript claims them, correspondence disclaims them; 6 of 54 checked names not importable from `RMQPaper` | Open — re-scope as a repository-surface question |
| `DD-C` | E1 disposition: banked non-public strengthening, **or** public landing as a full release candidate requiring the full release audit (accepted `P1-4`) | Open |
| `DD-D` | PRE rung + charge policy + **the fallback, decided in advance**: "the payload is built by a closed program over a pointwise-encoded input, whose emitted writes reproduce the canonical payload words in order" — a **provenance** claim with no cost claim. Deciding it in advance removes the incentive to weaken `O-WORKCAP` later, which is exactly what v5's drop of that obligation illustrates | Open — adopt only with C1–C4 frozen first |
| `DD-E` | Workspace measure: representation, encoding, **peak-live-state measure, and a proved encoding bound**. Until all four, the `2n` forecast is removed, not restated | Open — DD'd before any lane work |
| `DD-F` | **Venue.** The ITP 2027 February deadline and anonymisation requirement are **inherited from the 2026 call**; the auditor found only a call for bids for 2027 and the official series page still lists ITP 2026 as next. **This puts the project memory "ITP 2026 has passed; target ITP 2027" in question** — v4 restated that quarantined sentence as fact. No calendar governs until DD-F. **Building the anonymised bundle proceeds regardless**, being prudent under either venue | Open |
| `DD-G` | *(unused — reserved so v4's misuse of `DD-G` for Venue cannot be silently reintroduced)* | — |
| `DD-H` | POSIX containment (§I) | Open |

---

## C. The PRE contract

**Contract B, repaired.** Quoted in full, because v4 and v5 both cut this sentence at exactly
the clause that exposes the gap below:

> "CONTRACT B IS STRONGER, but neither is freezable as written: each has exactly
> one fatal hole, and they are mirror images, **so the correct frozen artifact is
> B repaired with A's Group A plus one obligation neither contract contains.**"

v5 replaced that comma with a period and stopped. The dropped clause names the
missing obligation; it is `O-WORKCAP` below, and v5 did not carry it.

### C.1 The generation rule, and the coverage gap it does not close

**One obligation per fake that SURVIVES the adopted contract.**

Measured from the catalogue: 15 distinct fakes (`FK-1`..`FK-9`, `FK-11`..`FK-16`;
**`FK-10` does not exist** — 16 is the highest label, not a count), 25 rows, 14
surviving / 11 killed. Against contract B: 12 rows, **5 survivors — FK-3, FK-5,
FK-7, FK-9, FK-14**.

**FK-7 survives contract B and no obligation kills it.** `O-REPLAY` is a
non-goal and disclaims the kill; the content that would close it is distributed
across `O-UNIF`, `O-FIREWALL`, `O-WORKCAP`, `O-NOINHERIT` and `O-POINTWISE`, and
the catalogue does not say that distribution suffices. Recorded as an open gap
inside the rule, because v6 stated the rule, left this hole, and disclosed only
the other one.

**Three fakes were never run against contract B at all: FK-11
(`DESCOPE-AND-STILL-CLAIM`), FK-12 (`TraceEvent WIDTH-CERTIFICATE ARM`), FK-13
(`O12 CITES A THEOREM THAT DOES NOT EXIST`).** All three survive contract A. Under
a rule measured on B's rows they generate zero obligations and the completeness
check reports complete — the exact green-artifact failure the rule exists to
prevent, inside the rule.

**Therefore the freeze precondition is: 15 of 15 fakes have a contract-B verdict.**
Running FK-11/12/13 against B is scheduled work, not an assumption, and the
contract cannot be frozen while any fake lacks a verdict.

### C.2 Obligations

| id | obligation | kills | basis |
|---|---|---|---|
| O-UNIF | **Program uniformity** — single closed constant, length `rfl`-pinned, static program bits `< \|payload(n)\|` | FK-5 | `R1 [B, FATAL]` |
| O-WORKCAP | **Reflected ISA with a literal per-instruction work cap.** The interpreter must be DATA, not a Lean function: `inductive Prim` over `constZero/succ/add/sub/mulConst/divConst/lt/le/eq/getBit/setBit`; constructor-exhaustive `Prim.constants` and `BInstr.semantics`, no wildcard; and three theorems, of which `bstep_reflects : forall i s, bstep i s = interpretPrims i.semantics s` is the one that stops `semantics` from being a decoration, `semantics_cap : forall i, (i.semantics).length <= primCap` with `primCap` a **literal**, and **`prim_const_cap : forall i, forall p in i.semantics, forall c in p.constants, c < 2 ^ wordBits`** -- the row that stops the payload being smuggled in `mulConst (c : Nat)` / `divConst (c : Nat)` constants, which `O-UNIF`'s program-bit budget does not see because it bounds the PROGRAM, not the interpreter. `Prim` carries **no table-lookup constructor and no unbounded `Nat` payload**, and `R1`'s budget extends to `isaBits + progBits < payloadBits`. | FK-3 | `R2 [A AND B, FATAL]` |
| O-BITS | **Bit-accounting with no fittable parameter.** `REQ-BLD-07`'s third conjunct is satisfiable by `rfl` when `paddingBits` is derived from the write log. Delete the bit-sum equation; replace it with a sequence equality in emission order (`builder_writes_canonical_words`, mapping each segment's written words onto `canonicalSegmentWords`) plus a width row (`builder_write_width`). Bit count and padding follow as corollaries and **`paddingBits` is never a free parameter** | FK-9 | `R3 [B]` |
| O-SCRATCH | **Scratch-memory row** — bounded, or its absence stated | FK-14 | `R10 [BOTH]` |
| O-REPLAY | **Replay is not the anti-oracle** — stated as a non-goal. Kills nothing on its own: `R11` says replay is "necessary, nearly free, and insufficient", and locates the anti-oracle content in program uniformity (`O-UNIF`), the interpreter firewall (`O-FIREWALL`), **the reflected work cap (`O-WORKCAP`)**, no-inheritance (`REQ-BLD-06`'s third conjunct, `O-NOINHERIT`) **and the pointwise input encoding (`REQ-BLD-08`, `O-POINTWISE`)**. | — | `R11 [BOTH]` |
| O-NOINHERIT | **No inheritance** — `REQ-BLD-06`'s third conjunct, named explicitly rather than inherited, on the same principle `O-FIREWALL` is named | — | `R11 [BOTH]` |
| O-POINTWISE | **Pointwise input encoding at fixed width** — `REQ-BLD-08`, the third inherited contract-B row R11 names. Also carries `R1`'s header clause: the input length arrives in a register read from a pinned header cell, `(encodeInput xs).readWord? inputSegment 0 = some (encodeInt wordBits xs.length)`, with the element cells shifted by one. v2's C1 had the header clause; v5 and v6 both lost it | — | `R11 [BOTH]`, `R1` |
| O-FIREWALL | **Import firewall, CI-enforced** — closure pinned to `{Cost, RAM, WordRAM}` | — | **Contract B already carries this as `REQ-BLD-13`**; it is why FK-2 does not survive B. Retained as an explicit obligation so the property is named rather than inherited. `R5` is the contract-A mirror and is **not** the basis here |
| O-CONTROL | Current-repo-shaped oracle **negative control, as a checked theorem rather than a placeholder**, with two named exhibits: `not exists ps : List Prim, ps.length <= primCap and interpretPrims ps = oracleSemantics`, and a baked-constant-table `builderProgram` variant proved to violate `R1`'s information gap. | — | `R12 [BOTH]` |
| O-REPR | **Signed-word representability** of every input and compared operand at the declared width, with a comparison/order refinement theorem and an exhibited satisfiable all-size family. **Absent this, public wording says "unit-cost comparison oracle"** | — | accepted `P1-7` |
| O-WRITE | One shared payload sub-builder. Physical-store emission **and packed memory construction** separately costed **and joined**, with **write units stated**: bits counted in bits, or words counted in words with an exact concatenated-bit-length and an address/value replay. The units clause IS the repair — "charged writes = payload bit length" is dimensionally wrong. | — | accepted `P2-2` |
| O-COUNT | Report **five wrappers / eight encoded tables**; no `2n` forecast until DD-E | — | accepted `P2-3` |

The catalogue **is** a governed artifact committed *with* this revision --
not at the verification pin, per the header rule:
`docs/internal/wf3_attack.json` is committed, so every `FK-` and `R` claim in
C.1 and C.2 is checkable against a SHA rather than against a file in a session
directory. It was on no ref through v2-v13, and v4 asserted it was "committed
under `docs/internal/`" while contradicting that in the next sentence -- which is
why H item 5 existed. That item is now done at the revision-introducing commit, and the
contract-freeze precondition it named is met there.

### C.2b What C1–C4 are

v5 used "C1–C4" four times and defined it nowhere; `DD-D` and non-goal 10 both
gate on it. Per `wf3_attack.json` `R13`, the four contract rows that must land and be
blind-audited before builder construction begins are **`R1`, `R2`,
`R5`/`REQ-BLD-13`, and `R12`** — `R13` states that ordering itself; the
aggregate-gate step is this plan's addition —
in this plan's obligation names: `O-UNIF`, `O-WORKCAP`, `O-FIREWALL`,
`O-CONTROL`. The remaining obligations are required but are not the freeze set — **with one
correction**. `R1`'s header clause (input length read from a pinned header cell)
is carried in `O-POINTWISE`, which sits outside the freeze set, so C1 could land
with `R1` only partly discharged. That clause is therefore **also** a C1
obligation, and `O-POINTWISE` is jointly owned by C1 and R11. v2's C1 has that clause
inside the gate, and it belongs there.

### C.3 Freeze order

C1–C4 land, are gated, and are **blind-audited before one line of builder
construction is written**. The author-run completeness check (§C.1) is a
precondition for requesting that audit, never a substitute for it; it is
recorded in `docs/internal/DESIGN_DECISIONS.md` as a dated entry naming the
15-of-15 verdict table, owner: coordinator. No checker enforces it and none is
claimed to.

The blind audit of the contract is a required node, not an optional one.
External adversarial review has caught this program's defect class more
reliably than anything else — though **not uniquely**:
`PLAN_AUDIT_DISPOSITION.md:236` records accepted `P2-1` as "Partially
self-identified before the audit". Replacing that node with an author-run
self-check would be a regression.

---

## D. Non-goals (all ten from v2 §6, plus two)

1. Closure-minimization campaigns beyond the DD-A probe.
2. A second *paper* root.
3. **C/Rust generation** (also frozen by the roadmap, §0).
4. Resuming the banked architecture threads.
5. **S1 in any form.**
6. Asymptotic-only preprocessing claims.
7. **Renaming frozen public identities** — the frozen executable name
   `rmq_e1_machine_validate` is preserved; an alias may be added, **never a
   rename** (accepted `P1-8`).
8. Touching frozen requirement wording — appended amendments only.
9. **Advertising replay as the anti-oracle.**
10. Any preprocessing claim that outruns C1–C4.
11. **Charging the existing shape builder.** `RMQ/Core/Shape.lean:654-677,892-901`
    with the analysis at `PLAN_AUDIT_DISPOSITION.md:170-185`: `insertRightStack`
    is the quadratic construction -- `:675-677` alone is only the wrapper, and the
    cost comes from the spine walk, `plugRight`'s rebuild, and `buildTreeAux`
    calling it per element; accepted `P1-5` found the
    linear proof **impossible** for it. The lane is a persistent monotone-stack
    scan or a direct shape emitter, **and must prove value agreement with the
    canonical shape**.
12. No new instruction primitive or cost model before the reversal act (§0).

---

## E. E1

All-row adjudication covering all 11 REQ rows, the inherited INV rows, the CHK
rows, `REQ-E1-09`, `L-OPEN-06`, the evidence matrix **and every current-fact
surface**, disposed atomically (accepted `P1-2`). Parallel to PRE, not
behind it — no disposition creates
that dependency, and PRE is the track whose acceptance criterion was withdrawn
(`P0-1`). At the pinned commit the matrix is the frozen pre-implementation
version: 24 rows `Open`, 0 `SATISFIED`. The 8-of-24 figure describes `648e512`
and is labelled as such wherever it appears. `REQ-E1-09` is the only
public-surface row.

Root checks (accepted `P1-8`): import **only** that root; exact declaration
inventory; count floor; deletion mutation; anti-empty control. Packet manifest and
operational-surface list are **enumerated, not counted**.

**The retired narrative stays retired** (accepted `P1-3`): the public wording is
"two independent operational refinements connected to the same public RMQ
semantics". "One protocol" may be used **only** after a checked join theorem,
reconciled with `scripts/independence_check.lean`. v5 mapped this finding to §E
and put nothing here.

`M1 → S1` is retained explicitly as a **deferred, non-gating edge**; S1 and PRE
**neither discharges the other** — not "zero proof obligations"; and "zero-paper-facing" is stated as **"no
positive paper claim"** (accepted `P3-1` — v6's §A row promised this wording and
§E did not carry it).

E1's public landing is `DD-C`, not a default.

---

## F. Measurement and roadmap hygiene

`P2-1`: one **committed** script emits separately named fields — root-inclusive
files, imported dependencies, physical lines, non-blank lines — with wrapper,
off-by-one and blank-line mutation controls. **No percentage is quoted without its
unit.**

`P1-6`: `docs/internal/RMQ_FINAL_ROADMAP.md:452` still reads "Four
reviewer-facing surfaces currently disclaim this capability", false at this tree.

**The repair is not "change Four to Nine".** The disposition requires the
inventory to be **derived from `docs/internal/CLAIM_DRIFT_POLICY.json` at the
pinned commit, with a per-path disposition, and no fixed count pinned anywhere** --
because a check pinned to four would pass while a fifth surface went stale. v6
carried only the escalation and left the operative half out, which would have
been discharged by editing a numeral. Owner: coordinator, §H item 4.

---

## G. Effort figures

Session figures are **planning hypotheses, relabelled not deleted**: `~9–13
sessions` (`docs/internal/RMQ_PROGRAM_PLAN_2026-08-13.md:269`), `9–13 worker + coord +
external audit` (`:363`). **Gates use the upper estimate plus an audit buffer.**
No calendar governs until `DD-F`. Calendar gates update only from an official
2027 CFP -- accepted `P2-4`, the rule §A.1 maps to this section.

---

## H. Before the tag

1. Commit the fresh-blind audit reports. **No V1 RC report has ever been
   committed on any ref** — 26 distinct reports plus a `README.md` index exist
   under `docs/internal/audit_reports/` across all refs (15 plus the README at
   this commit), and none is an RC-1/RC-2/RC-3 report.
2. Round-log entry in `docs/internal/AUDIT_AND_A_DESIGN.md`.
3. **Rerun the entire aggregate gate from a clean exact checkout** on the tree
   to be tagged (RC-3 `P1-3` tail).

   Two independent reasons, and v9 gave only the weaker one. The topology
   deadline moved 300→900, which invalidates the previous full run. **And the
   aggregate was actually FAILING**: WDD-20260816-043 records that
   `claim_drift_policy_regression.ps1` exited 1 with 23 fixture failures from
   `804c58c` — the round's first commit — through thirteen further commits and
   three audit rounds, because the round-1 scanner change suppressed the
   `[allowed]` lines 23 fixtures assert. It survived because **nobody ran the
   aggregate**; a green per-commit governance check stood in for "releasable".
   Repaired in `d31064c`. That is the stronger argument for the rerun, and v9
   omitted it — mentioning round 4 once, for a different reason.
4. Repair `RMQ_FINAL_ROADMAP.md:452` (§F).
5. ~~Commit `wf3_attack.json` **and both dispositions** --
   `PLAN_AUDIT_DISPOSITION.md` and `RC3_DISPOSITION.md` -- under
   `docs/internal/`.~~ **DONE in the commit that introduces this revision**, together with this plan,
   `PLAN_LINEAGE.md` and `RMQ_PROGRAM_PLAN_2026-08-13.md`. The two dispositions
   supply every one of the 24 accepted findings in A.1 and A.2, plus
   `RC3_DISPOSITION.md` section 5 item 11, which A.2's second table carries as a
   separate accepted item and which the 24 does not include. The item is kept
   rather than deleted because other items are cited by number.
6. **`scripts/paper_root_measure.ps1`** — the committed measurement SCRIPT
   required by accepted `P2-1`, emitting root-inclusive files, imported
   dependencies, physical lines and non-blank lines as separately named fields,
   with wrapper, off-by-one and blank-line mutation controls, quoting no
   percentage without its unit. Its subject is the **paper-root import closure**
   (204 files / 202,096 lines), not E1. Owner: coordinator. v5 scheduled nothing;
   v6 and v7 scheduled a `.md`, which emits no fields and hosts no mutation
   control — a path that cannot discharge the obligation it is scheduled for.
7. **Synchronize the packet manifest and both roadmaps** — the packet currently
   ships the stale DAG (accepted `P3-1`). Owner: coordinator.
8. ~~**Expected-type consumers for the standalone lower-bound, List-Int and
   readWord aliases** (accepted RC-3 `P2-3`), on the
   `PackedCellProbeExpectedPaperType` precedent: an independently written `Prop`
   inhabited by the alias alone, verified to fail closed under mutation.~~
   **DONE at `15865e1`** (DD-20260816-117, WDD-20260816-053). Four mutants —
   loosening the slack coefficient from `2` to `3`, the `2n` witness, the `2n`
   space bound, and turning the word-width bound strict — each REJECT. The item is kept rather
   than deleted so the record shows what the round closed. Items are cited by
   number elsewhere, and a stable numbering keeps any future deletion from
   redirecting them — though nothing cites this item or the one after it, so
   deleting it would in fact have redirected nothing. Which sections those
   are is deliberately not listed here: that list would need maintaining on every
   edit, which is the species `PLAN_LINEAGE.md` records as 3.
9. Then cut `audit-v1-rc-4` with an identity-and-scope-only annotation, rebuild
   the packet, and commission a fresh auditor.

Scheduled after the reversal act, not before the tag, but named here so they are
not lost: the **`DD-A` capstone-seam feasibility probe** — a scratch feasibility
port with an exact-type check and a closure measurement, for which
`PLAN_AUDIT_DISPOSITION.md:102-105` **lifts the Core-restructuring non-goal for
that probe only**; and the **anonymised bundle**, which `DD-F` says proceeds
under either venue. v5 asserted both and scheduled neither — and, by freezing
Core work with no exemption, made `DD-A` unreachable by its own text.

---

## I. `DD-H` — the POSIX barrier cannot contain a `setsid` descendant

`WORKFLOW_DESIGN_DECISIONS.md` (WDD-20260816-039) records this as **found and not
fixed**. `Stop-RMQPosixOwnedProcessGroup` is `kill(-groupId, signal)` and is the
only containment mechanism on that path; a descendant calling `setsid` is outside
the signalled group **by construction**. `Invoke-RMQOwnedProcessEscapeProbe`
exists, **is not wired into the gate, and has never been executed**; its expected
outcome on Linux is `ESCAPED`.

The honest statement, which must not be softened: **owned-tree containment is
demonstrated on Windows and demonstrated only for group-resident descendants on
POSIX.**

RC-3 `P2-5` required a Linux self-test **and** "either adopt a containment
mechanism that survives the escape or track descendants recursively". Only the
probe exists, so **`P2-5` is not discharged** — §A.2 says so rather than counting
it among the closed.

Actions: run the probe on Linux and record the result; then decide whether to
close the hole before V1 (POSIX descendant enumeration via `/proc`).

---

## J. Rules this program keeps re-learning

1. **A checker is worth exactly what it measures.** The citation checker's worst
   case was narrowed twice by successive audits, and a third then found that
   field ASSIGNMENTS (`name :=`) still counted as declaration sites. **The
   figures are deliberately not restated here.** They live in
   `docs/internal/WORKFLOW_DESIGN_DECISIONS.md` (WDD-20260816-041, -042, and
   -045, which corrects one of them), they are not derivable from this plan, and
   a copy of them here goes stale the next time that record is corrected —
   which is `PLAN_LINEAGE.md` species 3, in the item that names it.
2. **A repair reported without a measurement that could have failed is not a
   repair**, and the measurement must be of the right quantity. Three no-op
   patches in one round printed success.
3. **Fixing a claim at its origin is not fixing the claim.**
4. **An enumeration of one's own errors is a claim and can be incomplete.** Round
   1 named three stale statements; there were four. Hence §A.
5. **A rule nobody checks is violated while being stated.** "No other status is
   permitted" was violated twice over nine days.
6. **Line pointers rot, and so does any tally kept beside the list it tracks.**
   No count is given for the instances below, deliberately: a hand-maintained
   total is the same kind of object as a line pointer, and this program has
   repeatedly got such totals wrong (`PLAN_LINEAGE.md`). The instances:
   `L-UB-06` (~1,090 lines off); the producer pointer wrong **three times**
   (`:702` → `:723` → `:752`); the evidence-matrix counts;
   `docs/PAPER_CLAIM_CORRESPONDENCE.md:115` (`:490`→`:498`); two roadmap-range
   citations in superseded revisions; and DD-20260816-111's own citation
   `EVIDENCE_MATRIX.md:140`, which resolved at no commit. `paper/check_citations.ps1` covers **`paper/THEOREM_LEDGER.md`
   only** — `PAPER_CLAIM_CORRESPONDENCE.md` and this plan are unchecked citation
   surfaces. Extending the checker to them is open work, not a completed claim.

---

## 0. The governing constraint

`docs/internal/RMQ_ENDGAME_ROADMAP.md:752-761` is the frozen list — **ten items**.
The five bearing on this plan:

> `:755` — merge or forward-port of `` `648e512...` ``;
> `:756` — public Core/B1 rewrite in service of a validation-local obstacle;
> `:757` — new instruction primitives or a new bespoke cost model;
> `:758` — A1 module refactor and broad renaming;
> `:759` — C/Rust backend work;

The ellipsis in `` `648e512...` `` is the roadmap's own text. It denotes the tip
of `claude/b1-b2-charged-fringe-tables`, which is exactly what bare `648e512`
resolves to — **one object, not two**. Its *diff* is two files ("Repair two
axiom-check scripts left stale by the 76 -> 210 migration").
§E uses bare `648e512` as that branch tip — the same object.

PRE's builder contract is a new instruction primitive set and a new cost model,
frozen by `:757`. G1/Core restructuring is tested against `:756` and `:758` before
it starts; work requiring facts re-derived from lower-level modules is **new proof
work, not re-plumbing** (`PLAN_AUDIT_DISPOSITION.md:97-100`).

**The freeze does not lift itself.** `:763` — "This freeze is reversible after
V1." Reversible requires an act. After `V1 ACCEPTED` the owner records a dated
reversal decision in `docs/internal/DESIGN_DECISIONS.md` naming which frozen items
are unfrozen; absent that entry the freeze holds regardless of the verdict. No
checker enforces this and none is claimed to — it is a convention with a named
location, which is the most this plan can honestly assert about itself.

### Sequence

```
RC-4 ─► fresh-blind audit ─► V1 ACCEPTED ─► owner reversal act (DESIGN_DECISIONS.md)
                                                    │
        ┌───────────────────────┬───────────────────┴───────────────┐
        ▼                       ▼                                   ▼
  PRE: C1-C4 freeze        E1 all-row                        G1 (tested against
   ─► BLIND AUDIT          adjudication                       :756 and :758)
   ─► builder construction
        ▲
        └── precondition: 15/15 fakes have a contract-B verdict
```

Everything before `V1 ACCEPTED` is release-synchronization and gate repair only.
PRE, E1 and G1 all sit after the reversal act, in parallel.

---

## K. Audit record, at its true scope

**Counts are given by naming artifacts, not by tallying.** Each artifact below
is named with its commit status, so a reader can tell what is checkable from
what is not. No count of plan audits is kept and no severity claim is made
about them: `PLAN_LINEAGE.md` keeps no count of them either, and says why
it will not maintain them. A count that nothing can check is a count that rots.

- Agent audits of the RC-4 candidate, each with a committed record in
  `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`, appended in round order starting
  at `WDD-20260816-040` (`:9889` at this pin). A round may append more than one
  entry, so the entry identifiers are not a round tally.
  **No count is given and no last entry is named**: the series grows every round,
  and both a tally and an endpoint pointer would need re-checking at each pin.
  That is `PLAN_LINEAGE.md` species 3 — and this entry carried both until
  2026-08-16, when the enumeration went stale one commit after it was written.
  The endpoint pointer did not — `:10127` is `WDD-20260816-043` at both commits.
- Fresh-blind plan audits with a committed report:
  `docs/internal/audit_reports/2026-07-25_A09_endgame_plan_audit.md`.
- The plan audit in `PLAN_AUDIT_DISPOSITION.md` (2026-08-13, artifact
  `RMQ_PROGRAM_PLAN_2026-08-13.md`, verdict `NOT_SOUND`) — the source of §A.1's
  fourteen accepted findings. Committed with this revision (H item 5).
- Agent audits of this plan itself: **no committed record**, and no count is
  kept, and no claim about their number or severity is made.

**Across the three V1 candidate audits, every finding was a claim, a checker, or a
process defect -- none was a defect in a kernel-checked theorem.**

**The RC-3 disposition behind that summary is committed *with* this revision,
not at the verification pin; the audit REPORTS are not.** So the summary is now checkable for RC-3 against
`docs/internal/RC3_DISPOSITION.md`, and remains uncheckable for RC-1 and RC-2,
whose material exists on no ref. v7 claimed the summary was "verifiable for
RC-3" via that file when the file was itself uncommitted -- the contrast it drew
was unsupported at the time and is supported now, by the commit rather than by
the argument v7 made. The report `RC3_DISPOSITION.md` cites at its own line 5,
`docs/internal/audit_reports/2026-08-15_V1_RC_fresh_blind.md`, still exists on no
ref; H item 1 covers it.

Not "no mathematics has ever failed": `docs/internal/audit_reports/2026-07-26_A10_f03_geometry_closure.md`
returns "Checked obstruction | **Not established**" and NOT CLOSED, and accepted
`P1-5` is titled "PRE-1's linear shape proof **is impossible** for the named
implementation".

Every RC-4 candidate audit round with a committed record found defects in work
its author had already verified; those records do not use severity labels uniformly, so no severity
claim is made here. The audits of this plan have no committed record, so this
document makes no claim about their number or severity. Where §Method
describes what they found, that description is marked UNVERIFIABLE there.
