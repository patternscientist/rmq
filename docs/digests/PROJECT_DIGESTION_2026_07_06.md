# Project Digestion 2026-07-06: State, Significance, and the Path to a Paper

**Audience.** A mathematically mature reader — comfortable with proofs,
asymptotics, and the idea of a machine-checked proof — who is *not* assumed to
know data-structures vocabulary (range queries, succinctness, word-RAM,
rank/select, amortized analysis), Lean internals, or anything about where
formalization research is published. Every such term is defined at first use;
if one is not, that is a defect in this document.

**Status.** Describes `main` at `3f6f1e3` on 2026-07-06. This is the canonical
current public project digestion on the publication branch. The coordinator
checkout's local `PROJECT_DIGESTION_2026_07_CURRENT.md` was used as
branch-local source material, but is not duplicated here; this dated digest is
the public current-state document, while older digests are historical
background. This is a teaching and orientation document; where prose and Lean
disagree, the Lean wins. The full first-contact treatment of the mathematics
and the cost model is
[`DEEP_PROJECT_DIGESTION_2026_06_28.md`](DEEP_PROJECT_DIGESTION_2026_06_28.md);
this digest updates the state (a great deal has landed since, including in the
last two days), ranks what has been achieved, and — new here — explains what
still separates the repository from a publishable research paper. It was
hardened by an adversarial review loop recorded in Appendix A.

**W19 supersession note (2026-07-13).** The statements below that `2^128`
survives only in compatibility variants describe the 2026-07-06 execution
route inventory. No current canonical execution theorem uses it as an
activation premise, but W19 now also uses symbolic `N = 2^128` in a proof-only
sparse-local nonvacuity witness. That witness is not an execution, payload,
cost, runtime, or paper theorem premise.

---

## 0. One paragraph

This repository is a machine-checked development, in the Lean theorem prover
(~170,000 lines, no unproved statements, no custom axioms), of a classical gem
of computer science: an array of `n` numbers can be preprocessed into a
bit-string of `2n + o(n)` bits — *discarding the numbers themselves* — from
which the position of the minimum of **any** sub-range can be recovered by a
bounded number of steps, independent of both the range's width and of `n`; and,
by a counting argument, no encoding scheme can beat the leading `2n` bits. Both
directions are proved. Over the past week the project's center of gravity
shifted from *proving the theorem* to *making the cost claim mean something*:
the query is now a concrete machine-like program whose every memory read is
logged, audited against a declared memory layout, and — the newest theorems —
provably dependent on nothing but the declared stored bits, with the model
bridge itself packaged as a theorem. The integrated branch now exposes a
route-split all-size theorem with fixed modeled constant `4144`; the older
`196727` aggregate remains only as legacy compatibility, and the
Ready-threshold fast-regime theorem has named cost `118`. Section 5 records
both the original gap analysis and the later closure.

---

## 1. What the project is

### 1.1 The problem

Fix a list of integers, say `xs = [3, 1, 4, 1, 5]`. A **range-minimum query**
(RMQ) names a contiguous sub-range and asks for the *position* of its smallest
value (leftmost such position, in case of ties). One query is trivial — scan
the range. The interesting object is a **two-phase data structure**:
preprocess `xs` once into some stored representation, then answer *every*
possible range query from that representation with a bounded amount of work
per query — bounded independent of the range's width *and* of `n`.

### 1.2 The classical theorem being verified

Two facts, both classical (1980s–2000s) and both verified here end to end:

1. **You may throw the numbers away.** Build a binary tree from the array as
   follows: the root is the position of the (leftmost) minimum of the whole
   array; its left subtree is the same construction applied to the prefix
   strictly left of that position, and its right subtree to the suffix
   strictly right of it. For `[3, 1, 4, 1, 5]`: the root is position 1 (the
   first `1`); its left subtree is built from `[3]`; its right subtree from
   `[4, 1, 5]`, whose root is position 3 (the second `1`); and so on. This
   tree is called the **Cartesian tree**, and its *shape* — the branching
   structure, forgetting all values — determines the answer to every range
   query. Two arrays with the same shape agree on all `~n^2/2` queries.
2. **The shape fits in `2n + o(n)` bits, with queries still constant-step.** A
   binary tree shape on `n` nodes can be written as a balanced string of `n`
   opening and `n` closing brackets — exactly `2n` bits. Storing the bracket
   string alone is not enough to answer queries *fast*: navigating it naively
   means scanning. The classical trick adds `o(n)` further bits of index
   tables so that navigation questions ("where is the bracket matching this
   one?", "how many closing brackets precede position `i`?") are answered in a
   bounded number of machine operations. Storage within a `(1 + o(1))` factor
   of the information-theoretic minimum, with fast queries, is what the field
   calls **succinct**.
3. **Matching lower bound.** The number of distinct `n`-node binary tree
   shapes is the Catalan number `C_n`, and `log2 C_n = 2n - 1.5*log2 n - O(1)`.
   Since distinct shapes give different answers to some query, any scheme that
   assigns to each length-`n` input a fixed-length bit-string from which all
   answers can be recovered must use distinct strings for distinct shapes —
   i.e. at least `log2 C_n` bits. So the `2n` of item 2 is optimal to leading
   order. (Scope: this is an *information-theoretic encoding* lower bound —
   how many bits any exact representation needs. It is not the stronger
   "cell-probe" style of lower bound that also constrains query *time*; the
   repository is explicit about this distinction.)

The repository proves item 2 as a public theorem over ordinary integer lists,
item 3 by building the Catalan counting from scratch, and — new this week —
fuses the upper-bound statement with its execution-model audit into one
headline, `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem`. Around this
central result (the "capstone"), the same toolkit has grown three reusable
side developments ("spokes"): bitvector dictionaries (defined in section 3.4),
the bracket-navigation layer the capstone needs, and a union-find spoke
(section 4, item 4) aimed at a different kind of theorem — amortized time.

### 1.3 What "machine-checked" buys, and what it does not

Everything above is a theorem checked by Lean's kernel (a small, independent
proof checker), depending only on Lean's three standard foundational axioms.
Continuous integration re-runs the check and also rejects every known
mechanism by which a statement could be accepted without a kernel-checked
proof (unproved placeholders, custom axioms, trusting the compiler instead of
the kernel, and so on). What it does **not** mean: nothing here claims that
compiled Lean code runs fast on hardware. All cost claims are theorems about
an explicit *cost model* — and that is where the interesting honesty problems
live, so the model is the subject of the next two sections. The accompanying
audit-driven-development provenance note is
[`../ADD_PROVENANCE.md`](../ADD_PROVENANCE.md); it describes process evidence,
not an additional proof object.

---

## 2. The honesty problem: why complexity theorems in a proof assistant are dangerous

Correctness theorems in a proof assistant are as trustworthy as its kernel.
*Complexity* theorems are not, by default, because "cost" is not a native
notion: the formalizer must invent the bookkeeping, and bad bookkeeping can
make a false-in-spirit claim literally true.

One Lean-specific fact is needed to see the danger. A data structure defined
in a proof assistant can bundle, alongside its actual data, arbitrary
mathematical objects and *proofs* as extra components — and those components
occupy no "space" and cost nothing to "consult" unless the model explicitly
counts them. The repository calls the components whose bits the space theorem
counts the **payload**, and the rest *proof-only fields*. Three classic
failure modes, all explicitly policed here:

- **Oracle smuggling (time).** Keep the precomputed answer to every query in a
  proof-only field, then "compute" it in one step by reading that field. The
  theorem "query cost = 1" is formally true and completely vacuous.
- **Certificate smuggling (space).** Claim `2n` bits of storage while the
  query secretly consults rich un-counted components.
- **Model gerrymandering.** Choose primitive operations so coarse that one
  "step" performs unbounded work.

The defenses, built in layers over months (the deep digest covers the earlier
ones in detail): a hard, audited line between counted payload and proof-only
fields; a cost-accounting trace discipline in which interpreter-generated
events are produced through checked constructors and then audited by provenance
theorems (for example, reads must match the store, successful reads must have
counted-payload backing, and the final trace has no synthetic cost-only
markers); a
sublinear-overhead predicate that is *proved* for the concrete overhead
function, so `o(n)` cannot hide linear data; and "anti-vacuity" theorems that
close degenerate readings (an example appears in section 4, item 3). The
newest layers — the reason this digest exists — take the final steps.

---

## 3. What landed since the last digest: the query is a machine program, provably

The 2026-06-28 digest ended with the query represented as disciplined
cost-counting callbacks. Since then, four milestones.

### 3.1 The whole query as one program with an audited memory trace

The final RMQ query is now a closed instruction-list program over a small
register state — concrete syntax, not a Lean function with hidden mathematical
power — evaluated by an interpreter against a read-only memory (the "store")
holding exactly the counted payload bits. The memory is divided into named
regions ("segments"), each an array of `w`-bit blocks called **words**; here
`w = log2 n + 1`, the standard choice (a word is just big enough to hold an
index — this is the **word-RAM** convention, the cost model in which results
of this field are normally stated: one read of a word, or one primitive
operation on a word, costs one step). Evaluation produces the answer *and* a
**trace**: the complete log of every memory read (segment, index, word
returned) and every word-level primitive used. Theorems then quantify over
that log:

- every logged read agrees with the one concrete payload store, whose layout
  (bracket string, navigation directories, with explicit offsets) is itself a
  Lean object;
- the addresses read are computed by the program syntax from the query
  arguments, with explicit no-overflow side conditions — closing the loophole
  where an all-knowing proof term hands the program exactly the right address
  and thereby smuggles in knowledge of the answer;
- no logged event is a "synthetic cost-only" marker. Backstory: during the
  migration to this trace discipline, older components were allowed to charge
  their legacy aggregate cost as a special marked event that carries cost but
  exhibits no memory activity. "Replaying" a component means replacing that
  marker with its actual logged reads and word operations. The theorem that
  the final all-size trace contains *no* marked events says: every unit of
  charged cost corresponds to an exhibited operation — nothing is billed
  without being shown.

### 3.2 The store-parametric capstone: the answer provably comes from the bits

One loophole survived all of the above: those theorems audit *the log of one
fixed evaluation*. A skeptic could still ask whether the value was somehow
determined independently of the memory, with the log as decoration. The
supplied-store theorem package
(`SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore`,
landed 2026-07-04/05) closes this by making the evaluator a *function of the
memory*:

1. **(Faithfulness)** For *every* store `S` — not just the intended one — each
   read event in the resulting log reports exactly what `S` contains at that
   address.
2. **(Canonical agreement)** Run on the real payload store, the evaluator
   coincides — value *and* log — with the audited canonical query, so all
   exactness and cost theorems transfer.
3. **(Store-parametricity)** If two stores agree on an explicitly listed
   **footprint** — a declared set of memory segments, with agreement required
   at every address inside them — the evaluator returns the same value and
   the same log on both.

Two remarks make this bite. First, the conjunction matters, not property 3
alone: an evaluator that ignored the memory entirely would also be
store-parametric, but it could not satisfy property 2's exactness on *every*
input array, because different arrays have different answers and the array
enters the evaluator only through the store. One fixed machine, correct for
all inputs, whose behavior is a function of the tape alone: that combination
forces the information to flow through the declared bits. Second — new this
week (2026-07-06) — the footprint is not decoration: a further theorem proves
every read the evaluator ever emits lies *inside* the declared footprint, and
consequently exactness and the cost bound transfer to *any* supplied store
that agrees with the canonical one there
(`RMQ.Headlines.succinctRMQFinalFullModelSoundnessExactOfFootprintGlobal`).
This is the formal analogue of handing someone a sealed machine and a tape
holding the `2n + o(n)` bits, and proving the machine's output depends on the
tape's declared region and nothing else.

What this does *not* discharge: the pricing. That one bounded-word read or one
single-word bit operation costs one step is the field's standard word-RAM
assumption, stated here as an explicit model rather than derived from
anything. The residual trust is the model; it is no longer the
implementation's honesty. (The footprint is also a safe over-approximation of
the addresses actually read, not proved minimal — stated, not hidden.)

### 3.3 The model bridge, packaged as a theorem surface (2026-07-06)

The obvious referee question — "why believe your bespoke cost bookkeeping
means anything?" — now has a Lean-level answer object rather than a prose
answer: a *model adequacy* packet
(`RMQ.Headlines.succinctRMQFinalTraceModelAdequacy`,
`...succinctRMQFinalFullModelSoundness`) proving in one place that the public
cost number is literally the length of the exhibited event trace (not an
opaque aggregate); that every event is a payload read or a bounded word
primitive; that successful reads carry explicit backing evidence into the
counted flat payload layout; that event data fit a stated finite bit width;
that no synthetic markers occur; and that the supplied-store story of
section 3.2 holds, footprint containment included. The accompanying
documentation states the non-claims with equal precision: no verified CPU or
compiler, no claim about compiled Lean execution speed, no minimal-footprint
claim.

### 3.4 Also since the last digest

The **rank/select** toolkit deserves its one-sentence definition here: over a
bit-string, `rank(i)` counts the 1-bits among the first `i` positions and
`select(k)` locates the `k`-th 1-bit; these two inverse-flavored primitives
are the workhorses of all bracket navigation above. The 06-28 digest listed
the *compressed* dictionary — one whose storage tracks the information content
`log2 (n choose k)` of a bit-string with `k` ones, beating `n` bits when the
string is sparse — as an open frontier. It has since **landed** as a public
family theorem with the full audit discipline (access/rank/select answered
exactly, at constant modeled cost, within the entropy budget plus `o(n)`).
And the repository has grown a reviewer-facing paper surface: a distilled
main-theorem statement, a related-work-and-limitations note, a citation file,
an AI-assisted-development disclosure, and a scripted reproduction pipeline
that rebuilds everything and re-runs all axiom audits in CI.

---

## 4. What has been achieved, ranked by significance

1. **A two-sided, machine-checked succinct-space theorem.** Mechanized upper
   bounds exist for several data structures; a mechanized *matching
   information-theoretic lower bound* — Catalan counting, built from first
   principles — is rare. The pair "optimal structure + proof that it is
   optimal," both checked, is the headline mathematical artifact (here
   "artifact" = the deliverable itself).
2. **The anti-oracle execution discipline.** As a recipe: *(i)* count payload
   bits, segregate proof-only fields; *(ii)* make cost logs unforgeable;
   *(iii)* represent the query as first-class program syntax; *(iv)* log every
   read and tie successful reads to offsets in one declared payload layout;
   *(v)* prove the evaluator is a function of the store, reads only within a
   declared footprint, and behaves identically on any store agreeing there;
   *(vi)* package the model bridge as a theorem. Steps (i)–(vi) are a
   transferable method for making complexity claims mean something in a proof
   assistant *without* building a verified compiler stack — arguably the
   project's main methodological export, developed under adversarial audits
   that repeatedly found and killed weaker designs (some preserved as
   theorems recording *why* they were insufficient).
3. **The compressed dictionary spoke** (section 3.4), including proved
   *negative* results closing tempting shortcuts — e.g., a theorem that a
   dense precomputed decode table necessarily costs a linear number of bits
   and therefore cannot hide inside the `o(n)` overhead. This is also the
   promised concrete example of an anti-vacuity theorem.
4. **A culture of self-diagnostic theorems.** The union-find spoke — a
   structure maintaining a partition of `{1..n}` under "merge two classes" and
   "name this element's class" — targets the celebrated result that its
   *amortized* cost (total cost of any `m` operations, divided by `m`, even
   though individual operations vary) is the inverse Ackermann function. It
   has not reached that theorem, and — unusually — it *proves* that its
   current accounting scheme cannot reach it: a collapse theorem showing the
   refined "potential function" (the standard bookkeeping device for
   amortized bounds) is extensionally equal to the naive one it was meant to
   improve on. Obstructions as theorems, not as TODO comments.
5. **Trust hygiene at scale.** ~170k lines, no external math library, three
   standard axioms only, CI-gated hygiene and per-spoke axiom audits, a
   scripted end-to-end reproduction pipeline, and public documents that state
   non-claims as prominently as claims.

---

## 5. What remains for publishable work

A candid gap analysis, updated for the last two days' landings; the venue
detail lives in [`../PUBLICATION_STRATEGY.md`](../PUBLICATION_STRATEGY.md).

### 5.1 Where such work is published, and the nearest prior art

Machine-checked mathematics and verified algorithms have their own venues: the
conferences **ITP** (Interactive Theorem Proving) and **CPP** (Certified
Programs and Proofs), and the **Journal of Automated Reasoning**. Papers there
are judged on what was formalized, how faithful the formal statement is to the
informal claim, what the effort revealed, and what is reusable; the venues
also review the accompanying code bundle (the "artifact," in that community's
second sense of the word).

The nearest published work is a 2019 Coq formalization (Affeldt–Garrigue–
Tanaka, ITP 2019) of rank/select and a simpler succinct tree encoding — with
runnable extracted code, but no RMQ, no cost story of this depth, and no lower
bound. ("Extraction" = mechanically translating the verified definitions into
a conventional language so they can be compiled and run.) The strongest
existing standards for *cost* claims are Nipkow's verified running-time
analyses (Isabelle), where cost is a function of the actual program, and the
Charguéraud-Pottier-Guéneau "time credit" line (Coq), which includes a full
inverse-Ackermann union-find verification. Against these, the deltas this
project would propose: the succinct RMQ result itself — upper *and* matching
encoding lower bound in one Lean development — subject to a referee-grade
novelty search before any priority wording is used, and the anti-oracle
discipline of section 4, item 2, as a method.

### 5.2 The former blocking gap: the constant split

The public all-size modeled query-cost bound is now `4144`, not the older
`196727` aggregate. The legacy theorem remains true and uniform in `n`, but the
new public theorem pays for the route the query actually takes rather than
summing mutually exclusive branch caps. R2 first exposed a route-split maximum
`65585`; R3 then proved the zero-block same-block route only needs a `4096`
machine-word chunk cap, lowering the clean public maximum to `4144`. The
repository documents why the constants have this shape, and one of this
digest's review rounds materially *corrected* the story, in the repository's
favor (Appendix A):

- The fast navigation path is proved applicable for **all `n >= 2^15`**
  (= 32768) — a modest, explicit threshold theorem
  (`concreteBPRelativeRmmInteriorReady_of_size_ge_readyThreshold`), not, as an
  earlier draft of the strategy documents had it, only from an astronomical
  `2^128` bound (that premise survives only in legacy compatibility variants,
  derived from the `2^15` theorem).
- Below the threshold, the query falls back to brute-force scans. These are
  *correct* because the fallback only triggers in regimes where the object
  being scanned is itself provably below the threshold — the capped scan is a
  complete scan, never a truncated one.
- The old `196727` bound was a single conservative *sum* of every branch's cap
  — three bracket-navigation accesses at 16, a zero-block scan cap
  `2*2^15 + 1`, an interior scan cap `4*2^15`, the fast interior path's 30,
  plus small change. The new route-split theorem keeps those routes mutually
  exclusive and exposed the R2 fixed all-size maximum `65585`; R3 then
  sharpens the zero-block cap to `4096`, giving the current fixed all-size
  maximum `4144`.
- The later integrated theorem surface states the regime split explicitly:
  `SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_of_size_ge_readyThreshold`
  proves the same final global trace costs at most
  `SuccinctFinal.concreteBPNativeSuccinctRMQFastRegimeQueryCost = 118` under
  `SuccinctClose.concreteBPRelativeRmmInteriorReadyThreshold <= shape.size`.

So the honest characterization is: constant-time is genuinely proved for all
`n`, with a public route-split all-size theorem and a smaller public fast-regime
theorem once the real machinery is engaged from a modest size. The zero-block
same-block branch is still handled by counted structural scanning rather than a
smaller constant-time small-block route, so tighter uniform constants remain
useful engineering; they are not the remaining paper-level proof blocker.

### 5.3 Expected but no longer blocking (largely landed 2026-07-06)

- **Model soundness packaging** — landed as the adequacy/full-soundness
  surfaces (section 3.3). The residual is *external* calibration: an
  executable reference interpreter or extracted code with benchmarks, which
  would decisively rebut "the model is fiction"; this remains the one item
  where the 2019 Coq work is ahead.
- **Distillation** — a fused single main theorem and a reviewer-facing
  theorem map now exist (`listIntSuccinctRMQPaperMainTheorem`,
  `docs/PAPER_MAIN_THEOREM.md`, `docs/PAPER_MODEL_ADEQUACY.md`). The remaining
  work is the paper prose itself, not the Lean surface.
- **Related work and limitations** — a first draft landed, correctly scoping
  the lower bound (encoding-counting, not cell-probe) and the non-claims. A
  literature-grade novelty search remains.
- **Artifact packaging** — reproduction script, CI workflows, citation file,
  and an AI-assisted-development disclosure landed. These are strong
  preparation; artifact-evaluation packaging, archiving, and review remain
  future work.
- **Effort narrative** — person-time, failed designs and why (unusually well
  preserved here as theorems); still to be written up.

### 5.4 What does not block

Correctness, kernel-level trust, hygiene, and honesty of statements are at or
above the field's bar today. The adversarial audits recorded in the round log
found the opposite failure mode more often: understatement.

---

## 6. Updated non-claims ledger (delta from 06-28)

Everything in the 06-28 ledger stands, with these updates:

- the compressed rank/select constructor is **no longer open** (landed
  2026-06-29 with the full audit discipline);
- the whole-query execution story is **no longer fixed-trace**: the evaluator
  is a function of the supplied memory, reads provably stay inside the
  declared footprint, and exactness/cost transfer to footprint-agreeing
  stores (2026-07-04..06);
- the model bridge is now itself a theorem surface, with explicit non-claims:
  no verified CPU/compiler, no compiled-Lean-execution claim, no
  minimal-footprint claim,
  no cell-probe lower bound;
- still true: no inverse-Ackermann union-find theorem; the word-RAM pricing is
  a stated model, not derived; no priority or novelty claim before a
  referee-grade search;
- newly explicit: the `196727` constant is correctly attributed to a
  conservative cross-regime sum with sub-threshold scan caps, the fast path is
  proved from `n >= 2^15`, and the integrated fast-regime theorem exposes the
  smaller `118` bound. An earlier `2^128`-gate characterization was too
  pessimistic and is corrected here and in the strategy document.

---

## 7. Skeptical questions, answered honestly

**"Constant time" with constant 196727 — is that a joke?** It is the honest
worst case of a statement that sums every regime's cap into one number. The
underlying design is the standard one — real machinery proved to engage for
all `n >= 32768`, complete (never truncated) fallback scans below — and the
integrated theorem surface now says the fast regime costs at most `118`.
Sub-threshold inputs are still scanned rather than table-looked-up, so shrinking
that fallback remains useful polish rather than the central remaining proof
obligation.

**Does store-parametricity really rule out oracles?** Combined with exactness
on every input, yes, for the value path: one fixed evaluator, correct for all
arrays, whose output is a function of the store's declared region — and whose
reads provably stay in that region — leaves the declared bits as the only
channel through which the answer can arrive. What it deliberately does not
address is *pricing*: that a word read costs one step is the field's standard
model assumption, stated as such.

**Couldn't the `o(n)` overhead hide the answers?** No — the overhead is a
concrete function proved sublinear (so it cannot be secretly linear), its bits
are counted payload subject to the same footprint discipline, and information
theory closes the back door: there are `~4^n / n^{1.5}` shapes, so answer
material for all of them cannot fit in `o(n)` bits.

**Is the lower bound the strongest one?** No, and the repository now says so
explicitly: it is the information-theoretic *encoding* bound (any exact
representation needs `log2 C_n` bits), matching the upper bound's leading
term. Time-space *cell-probe* lower bounds for RMQ exist in the literature and
are not mechanized here.

**Why hasn't anyone mechanized this before, if it's classical?** The
correctness is textbook; the difficulty is that the field's *claims* —
"succinct," "constant time" — are about models, and making those models
first-class, non-gameable proof objects is slow, adversarial work. That
difficulty is also the answer to "what is the research contribution": not new
mathematics, but a demonstration of what it takes for a proof assistant to
assert a complexity theorem *and mean it*.

**What single thing would most change an outside expert's assessment?** A
small (or honestly regime-split) constant. Second: runnable extracted code.
Everything else is presentation.

---

## Appendix A. Stress-test record (adversarial classroom loop)

Process actually followed, recorded honestly (the previous digest's audit
noted that self-reported stress rounds are unverifiable; this record therefore
names what each round changed, so the diffs are checkable against the text).

- **Draft 1** (2026-07-05) was written against `main` at `94ed811` from the
  repository documents and targeted source reading.
- **Round 1 — independent naive-reader review** (external reviewer pass, math
  PhD persona, no data-structures background). Verdict: structure and honesty
  good; the header's "every term defined before use" contract broken for
  roughly ten terms (succinct, word-RAM, word, rank/select, payload, trace,
  replay, extraction, artifact, segment); three passages unreadable for the
  target audience (the synthetic-marker sentence, the compressed-dictionary
  paragraph, the union-find item); one *logical* gap — store-parametricity
  alone does not exclude oracles; the conjunction with universal exactness
  does, and the draft skipped that linchpin; and two dangling questions in
  the constant discussion (why capped scans are correct; whether a fast-regime
  theorem exists). All folded into this revision: the definitions now appear
  at first use, section 3.2 states the conjunction argument, section 5.2
  answers both questions, and the method is stated as a recipe so it survives
  as a takeaway.
- **Round 2 — fact-check (partially external).** Two further reviewer passes
  (hostile-referee and repository fact-check personas) were launched and did
  substantial reading but were cut off by session limits before reporting;
  their briefs were then executed in-session against the Lean source. The
  material catch: draft 1 (and `PUBLICATION_STRATEGY.md`) claimed the fast
  path is only proved from `2^128 <= size`; the source proves it from
  `2^15 <= size`, with `2^128` surviving only in derived compatibility
  lemmas. This *strengthens* the repository's position and changes the
  correct referee-facing framing of the constant (section 5.2); the strategy
  document was corrected in the same commit. Also corrected: the footprint is
  a set of *segments* (with agreement at all addresses within them), not
  "segments and index ranges"; and the lower bound's scope note
  (encoding-counting, not cell-probe) was adopted from the new related-work
  document.
- **Round 3 — repository moved during review.** `main` advanced (`94ed811` ->
  `3f6f1e3`) with the model-adequacy/full-soundness surfaces, footprint
  containment, paper distillation documents, and the artifact reproduction
  pipeline. Sections 3.3, 5.3, and 6 were rewritten against the new state;
  the gap list shrank accordingly and section 5.2 became the target that later
  produced the fast-regime theorem.

Remaining objections after these rounds are, to this document's knowledge,
genuine open problems (external calibration, artifact packaging, tighter
uniform constants if desired, and the novelty search) rather than writing
defects.
