# Publication Strategy

What this repository would need to become a *paper-level artifact taken
seriously by the formalization research community* — grounded in specific
venues and pattern-matched against the extant work published there.

This is a strategy note, not a claim of current status. For what is actually
proved today, see [`WHAT_IS_PROVED.md`](WHAT_IS_PROVED.md) and
[`TRUST_AUDIT_PACKET.md`](TRUST_AUDIT_PACKET.md).

Date: 2026-07-05.

## 1. Where this work lives

The repository sits in the **mechanized-data-structures-with-cost** lineage. The
realistic venues, and the sitting precedent each would judge us against:

| Venue | Fit | Precedent it sits next to |
| --- | --- | --- |
| **ITP** (Interactive Theorem Proving) | **Best fit** | Affeldt, Garrigue, Tanaka, *Proving Tree Algorithms for Succinct Data Structures*, ITP 2019 (Coq: rank/select + LOUDS) — our nearest prior art |
| **CPP** (Certified Programs and Proofs, @POPL) | Strong, if an executable/programs angle is added | Verified-algorithm mechanizations with a functional-program flavor |
| **JAR** (Journal of Automated Reasoning) | Best for the *complete* story at journal length | Charguéraud & Pottier union-find (JAR 2019); Nipkow, *Amortized Complexity Verified* (JAR) |
| **FSCD / JFP** | If framed around functional analysis | Nipkow, *Verified Analysis of Functional Data Structures* (FSCD 2016) |
| **ESA / SODA / ICALP** (algorithms) | **No** | The mathematics is classical; a mechanization has no home there without a genuinely *new* bound |

## 2. The three reference lines we are measured against

1. **Affeldt, Garrigue, Tanaka — ITP 2019.** What a succinct-data-structure
   mechanization looks like *as a paper*: rank/select + LOUDS from Navarro's
   *Compact Data Structures*, extracted to executable OCaml. Our deltas:
   the RMQ / Cartesian / LCA succinct capstone (apparently not previously
   mechanized), a *matching information-theoretic lower bound*, and the
   anti-oracle Word-RAM cost discipline.
2. **Nipkow — *Amortized Complexity Verified* (ITP'15/JAR), *Verified Analysis
   of Functional Data Structures* (FSCD'16), and the 2024 ACM book *Functional
   Data Structures and Algorithms: A Proof Assistant Approach*.** The gold
   standard for verified *running time* of data structures. His cost is a
   function over the *actual functional program*. Ours is a modeled
   `Costed` / trace layer over proof-support structures that are not the
   executable artifact. Referees will ask why ours is faithful.
3. **Guéneau, Charguéraud, Pottier — *A Fistful of Dollars* (ESOP'18) +
   union-find inverse-Ackermann (JAR'19).** The gold standard for honestly
   stating `O(1)` / amortized bounds in a proof assistant: time credits tied to
   *real program steps*, with `O` formalized via filters. This is the bar for
   "is your `O(1)` real?"

Against those three, the genuinely novel contributions here — the paper's thesis
candidates — are:

- **(a)** first mechanized succinct RMQ **upper bound** `2n + o(n)`, `O(1)`;
- **(b)** a mechanized **matching lower bound** (rare: the three lines above are
  all upper-bound/correctness; a mechanized information-theoretic lower bound is
  a real differentiator); and
- **(c)** the **anti-oracle Word-RAM trace discipline** as a *method* for
  cost-honesty without an executable machine (first-order program syntax,
  trace-event cost, `eval_eq_of_readWord_eq`, store-parametricity).

## 3. What is missing for paper-level, prioritized

### P0 — blocking (a referee rejects without these)

1. **Resolve or defend the cost model constant.** The concrete query-cost
   constant is `196727`. *(Correction, 2026-07-06: an earlier revision of this
   document said the clean `O(1)` replay is "gated on `2^128 <= shape.size`."
   That was too pessimistic: the source proves the fast interior path applies
   for all `shape.size >= 2^15`
   (`concreteBPRelativeRmmInteriorReady_of_size_ge_readyThreshold`); the
   `2^128` premise survives only in derived legacy compatibility lemmas.)*
   The actual situation: the fast path is proved from the modest threshold
   `2^15`; below it, correct capped brute scans; and the public bound is a
   single conservative *sum* of every branch's cap (`3*16` close accesses,
   `2*2^15 + 1` zero-block scan, `4*2^15` interior scan, `30` fast interior,
   plus small change), with **no public regime-split theorem** stating the
   small cost once the machinery engages. Resolve by, in increasing ambition:
   - **(i)** state the regime-split bound ("for `n >= 2^15`, cost `<=` a few
     hundred") from the existing component facts;
   - **(ii)** tighten the cross-branch sum to a maximum;
   - **(iii)** replace sub-threshold scans with classical small-block table
     lookup, shrinking the uniform constant to something presentable (the
     modeled word size `log2 n + 1` already supports this).

   The repository is already honest *about* the constant; the paper must
   *resolve or precisely split* it, not merely disclose it.
2. **A soundness bridge for the cost model.** Nipkow's cost *is* the program;
   the time-credits cost *is* steps. Ours is a bespoke trace semantics. State and
   prove a theorem relating modeled trace cost to a *standard* Word-RAM step
   count, or to an executable reference interpreter that can actually be run. The
   anti-oracle boundary is a strong *ingredient* — it rules out reading the
   answer out of a proof-only oracle — but it is not yet packaged as a stated
   soundness result. Frame it as one.
3. **Distill to ONE theorem plus a one-page model.** A paper has a single
   headline (here: upper `and` lower), the model defined in roughly a page, and
   the ~40 headline aliases pushed to an appendix / the artifact. The current
   theorem surface signals "in progress"; distillation is mandatory.

### P1 — strongly expected

4. **A real related-work section** positioning the anti-oracle discipline
   against time-credits and Nipkow-style running-time functions, and the
   succinct content against Affeldt and Navarro's book. Argue precisely why the
   trace model is a *distinct, defensible* point in the design space, not a
   weaker one.
5. **Effort and reusable-methodology narrative.** Formalization papers are half
   about the *experience*: lines of code, person-time, what was hard, and what
   reusable infrastructure resulted. The `Costed` / RAM hub plus the anti-oracle
   layer is the methodological product — present it as such.
6. **Fidelity-to-textbook check.** Show the mechanization follows Fischer-Heun /
   Bender-Farach-Colton and surface the assumptions the informal proofs gloss.
   This is a classic ITP/CPP selling point.

### P2 — elevates to a strong accept

7. **Extract an executable and benchmark it.** This decisively answers the
   "modeled cost is not real" objection and is the cleanest path to CPP. The Coq
   succinct-DS line extracts to OCaml; we currently extract nothing.
8. **Artifact Evaluation.** We are close: CI, `scripts/gate.ps1`, and
   `#print axioms` checks already exist. AE badges are standard at ITP/CPP, with
   Lean artifacts archived to Zenodo / Software Heritage (e.g. ITP 2025
   entries). But AE-ready is the last mile, not the thesis.

## 4. The single highest-leverage move

**Make the constant honest at statement level: a public regime-split (or
genuinely small uniform) query-cost theorem.** Everything else (distillation,
related work, extraction) is tractable engineering. The five-digit constant is
the one thing that, left as-is, invites a referee to ask "did you formalize
the hard part, or cap your way past it?" — the true answer ("formalized, and
engaged from `n >= 2^15`") must become a theorem, not a conversation.

## 4a. Status update (2026-07-06)

Landed on `main` since this document was written (through `3f6f1e3`):

- **P0-2 (soundness bridge), internal half:** the model-adequacy /
  full-model-soundness surfaces
  (`RMQ.Headlines.succinctRMQFinalTraceModelAdequacy`,
  `...succinctRMQFinalFullModelSoundness`), plus footprint containment (every
  emitted read provably lies inside the declared footprint) and
  exactness/cost transfer to footprint-agreeing supplied stores. The
  *external* half — extraction / executable reference with benchmarks —
  remains open (P2 item 7).
- **P0-3 (distillation), Lean half:** one fused headline
  (`RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem`) plus
  `docs/PAPER_MAIN_THEOREM.md`, `docs/PAPER_MODEL_ADEQUACY.md`,
  `docs/PAPER_THEOREM_MAP.md`. Paper prose remains.
- **P1 item 4 (related work):** first draft landed
  (`docs/RELATED_WORK_AND_LIMITATIONS.md`), including the correct scoping
  that the lower bound is encoding-counting, not cell-probe (Liu-Yu/Liu).
  A referee-grade novelty search remains.
- **P2 item 8 (artifact):** reproduction script, CI workflows, `CITATION.cff`,
  and an AI-assisted-development disclosure landed.

Remaining, in priority order: **P0-1 (the constant, as corrected above);
extraction + benchmarks; novelty search; the paper itself.**

## 5. Recommended target

**ITP**, with the thesis: *the first mechanized succinct RMQ — upper bound
`2n + o(n)` / `O(1)` and a matching Catalan lower bound — in a Mathlib-free
Lean 4 development, using an anti-oracle Word-RAM trace discipline for
cost-honesty.* The lower bound and the anti-oracle method are the deltas over
Affeldt ITP 2019, contingent on closing the P0 cost-model gap.

## References

- R. Affeldt, J. Garrigue, K. Tanaka. *Proving Tree Algorithms for Succinct
  Data Structures.* ITP 2019.
  <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2019.5>
  (code: <https://github.com/affeldt-aist/succinct>)
- T. Nipkow. *Amortized Complexity Verified.* ITP 2015 / JAR.
  <https://www21.in.tum.de/~nipkow/pubs/itp15.html>
- T. Nipkow. *Verified Analysis of Functional Data Structures.* FSCD 2016.
  <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2016.4>
- T. Nipkow et al. *Functional Data Structures and Algorithms: A Proof Assistant
  Approach.* ACM Books, 2024. <https://dl.acm.org/doi/book/10.1145/3731369>
- A. Guéneau, A. Charguéraud, F. Pottier. *A Fistful of Dollars: Formalizing
  Asymptotic Complexity Claims via Deductive Program Verification.* ESOP 2018.
  <http://gallium.inria.fr/~agueneau/publis/gueneau-chargueraud-pottier-coq-bigO.pdf>
- A. Charguéraud, F. Pottier. *Verifying the Correctness and Amortized
  Complexity of a Union-Find Implementation in Separation Logic with Time
  Credits.* JAR 2019. <https://dl.acm.org/doi/10.1007/s10817-017-9431-7>
- *Verifying Datalog Reasoning with Lean.* ITP 2025 (current Lean-artifact
  norm). <https://drops.dagstuhl.de/storage/00lipics/lipics-vol352-itp2025/LIPIcs.ITP.2025.36/LIPIcs.ITP.2025.36.pdf>
- G. Navarro. *Compact Data Structures: A Practical Approach.* Cambridge, 2016.
- J. Fischer, V. Heun. *Space-Efficient Preprocessing Schemes for Range Minimum
  Queries on Static Arrays.* 2011.
