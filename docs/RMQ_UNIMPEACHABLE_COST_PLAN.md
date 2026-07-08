# The Unimpeachable RMQ Spoke: Executable Cost Evidence Plan

Goal, as stated by the project owner: the strongest version of the RMQ spoke —
one that minimizes "technically justifiable but reviewers must spend brainpower
auditing the justification instead of pattern-matching against precedent." In
particular: verify the cost story with extraction to runnable code **or
something similarly strong**, aligning the spoke with extant work so it is
without-question paper-level.

Date: 2026-07-07. Baseline: `codex/rmq-integrated-paper-frontier` @ `a2810d8`.
Runway: ~7 weeks at observed velocity (~3 weeks produced the current repo,
against 6–10 week external estimates), with Claude Max joining Codex Pro in the
loop within ~a week.

## 0. The load-bearing empirical findings (measured 2026-07-07)

1. **The cost story is already runnable.** Because the hygiene gate bans
   `noncomputable` and `partial`, the whole-query trace evaluator
   (`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult`) is computable
   Lean. A live `#eval` probe answered queries correctly with **38 trace
   events** at `n = 30` and **58 events** at `n = 120` — well under the
   fast-regime constant `118`, confirming the modeled caps are conservative.
2. **The bottleneck is construction performance, not computability.** The same
   probe at `n = 2000` did not finish in 8 minutes under the *interpreter*.
   Queries are cheap; building the Cartesian shape, payload, and tables is the
   hot path (list-heavy, likely superlinear constants; the interpreter adds
   ~2 orders of magnitude vs compiled `lake exe`).
3. Consequence: there is **no extraction gap to close — only an engineering
   gap**. Lean 4 natively compiles the *same definitions the theorems
   quantify over*. This is stronger in kind than Coq extraction (which adds a
   trusted extraction step); the precedent to cite is the verified
   reference-interpreter pattern (Watt's WebAssembly interpreter) plus
   standard Lean practice of shipping checked code as `lake exe` binaries
   (e.g. lean4lean).

## 1. What "unimpeachable" means, operationally

A referee calibrated by the three extant lines should be able to
pattern-match, not audit:

| Referee's pattern | Extant precedent | What we ship |
| --- | --- | --- |
| "The verified structure runs; they measured it" | Affeldt-Garrigue-Tanaka (Coq → OCaml extraction) | Compiled `lake exe` benchmarks of the *same* Lean definitions — no extraction step |
| "Cost is machine steps of a standard semantics, not bespoke combinators" | Verified reference interpreters (Watt); Isabelle Imperative-HOL time; time credits | A tiny standard word-RAM **machine** (small-step: pc / registers / memory array) with a proved simulation: machine steps = trace cost |
| "Constants are sane or honestly split" | all lines | fast-regime `118` already a theorem; shrink the `196727` uniform cap (sub-threshold table lookup) |
| "Claims map to checks" | AE norms (Zenodo, timings) | already done (`artifact/CLAIMS.md`); add Linux CI timings + DOI |

## 2. Workstreams

### Workstream A — Executable cost evidence (the centerpiece)

**A1. Compiled differential + cost harness (`lake exe rmq_bench`).** Extend the
existing `rmq_succinct_classic_validate` pattern to the *trace* path:
randomized and adversarial inputs; assert (i) answer = brute-force
`scanWindow`, (ii) trace length ≤ `196727` always and ≤ `118` when
`size ≥ 2^15`, (iii) no synthetic events; print measured trace-length and
wall-clock tables. Statement-level validation: this can catch a mis-stated
spec, which no theorem proved *via* the spec can.

**A2. Construction performance to `n ≥ 2^15` (and target `10^5–10^6`).**
Profile the compiled build path; replace hot list operations with
`Array`-backed **builder mirrors accompanied by agreement theorems**
(`fastBuild xs = concreteBPNativeSuccinctRMQPayload …`). No `implemented_by`,
no `native_decide` (both gate-banned): the fast builders are ordinary checked
definitions used by the harness, connected to the spec by equality theorems,
so the trust story is unchanged. Success gate: measured fast-regime queries
(`n ≥ 32768`) with trace length ≤ 118, benchmark curves flat in `n`.

**A3. Verified reference machine (the flagship strengthening).** Define a
minimal standard word-RAM as a small-step machine — program counter, register
file, flat word memory, ~10 instruction kinds (load, store-free reads, word
rank/select primitives, arithmetic on registers, conditional jump, halt).
Compile `concreteBPNativeSuccinctRMQWholeQueryProgram` (+ its register-program
leaves, which are already first-order syntax) to machine code; prove the
simulation theorem:

> running the machine on the payload memory produces the same answer, and its
> step count equals (or is bounded by a stated linear function of) the trace
> cost the public theorems constrain.

Then "constant modeled cost" is "constant steps of an ordinary machine
semantics that also runs." This removes the last bespoke element of the cost
story; the trace layer becomes an intermediate representation with a proved
bridge on both ends (spec above, machine below). Reuse the Phase-3 pattern
(leaf-by-leaf WithStore lifts) for the leaf-by-leaf compiler proofs.

**A4. Wall-clock separation discipline.** Benchmarks report (a) trace events
(model cost — theorem-relevant) and (b) wall-clock (artifact evidence —
explicitly not a theorem). Keep the two in separate table columns and separate
prose everywhere, preserving the repo's model/runtime firewall.

### Workstream B — Remove the remaining brainpower sinks

- **B1. Shrink the uniform constant.** Replace sub-threshold fallback scans
  with the classical small-block table lookup so the all-size constant drops
  from `196727` to something presentable (low hundreds). The `w = log₂ n + 1`
  model already supports it. This converts the deck/paper's longest caveat
  paragraph into one sentence.
- **B2. Retire the zero-block guard blemish.** Make the zero-block leaf decode
  from the supplied words outright (or prove the guarded and unguarded
  versions agree on footprint-agreeing stores), so the disclosed-edges list
  loses its most conspicuous entry.
- **B3. Uniform word-width side conditions.** Promote the trace-local
  event-width bound to per-component machine-word side conditions consumed by
  the headline theorems.
- **B4 (stretch). Exact dynamic read-set theorem** replacing the
  over-approximate footprint. Only if A-work finishes early; the
  over-approximation is disclosed and defensible.

### Workstream C — Precedent alignment and the paper

- **C1. Referee-grade novelty search** (protocol: AFP + Coq/Rocq package index
  + Lean libraries + ITP/CPP/JAR/JFR back catalogs + the Affeldt repo lineage;
  written summary with per-venue queries; then and only then settle priority
  language).
- **C2. Related work with real citations** (upgrade `docs/PAPER_RELATED_WORK.md`
  to BibTeX-grade; comparison table mirroring §1).
- **C3. Manuscript.** ITP submission shape: the two-sided theorem + the
  executable-cost story as co-headline, ADD as the process section,
  `artifact/CLAIMS.md` as the claim map appendix.
- **C4. Release artifact.** Zenodo DOI, Linux CI reproduction timings recorded
  in `artifact/README.md`, AE-style reviewer path (mostly exists), version tag.

## 3. Sequencing (7 weeks, two-assistant loop)

| Week | Codex Pro lane (proof/engineering) | Claude Max lane (coordination/audit/paper) |
| --- | --- | --- |
| 1 | A1 compiled harness; profile construction; A2 begun | Machine ISA design note (A3 spec); C1 novelty-search protocol + first pass |
| 2 | A2 to `n ≥ 2^15`; CI Linux timings; A3 machine semantics + rank-leaf compiler | Audit A1/A2 claims; C2 citation gathering |
| 3 | A3 leaf simulations (select, close/LCA legs) | B1 design audit; manuscript skeleton (C3) |
| 4 | A3 whole-query simulation theorem | B2 guard retirement worker + audit; paper §§1–3 draft |
| 5 | B1 sub-threshold table lookup (constant shrink) | B3 width side conditions worker + audit; paper §§4–6 draft |
| 6 | Polish; B4 only if ahead | C4 artifact freeze, DOI, timings; full-draft adversarial review round |
| 7 | Buffer: audit repairs | External red-team audit of paper+artifact; submission-ready tag |

Milestone gates: **M1** (end W2) fast-regime measurement exists — a compiled
run at `n ≥ 32768` showing ≤ 118 events; **M2** (end W4) machine-simulation
theorem checked; **M3** (end W6) frozen artifact + complete draft.

## 4. Risks and mitigations

- **Construction perf wall** (A2): if `10^5` proves hard, `n ≈ 2^15–2^16`
  already suffices for the fast-regime demonstration; Affeldt-line precedent
  does not demand large-scale benchmarks, only runnable ones. Mitigation:
  harness-only fast builders + agreement theorems; never touch the spec side.
- **Simulation proof size** (A3): the leaves are already first-order programs,
  and the Phase-3 store-parametric campaign (5 days) is the velocity
  reference for exactly this shape of work. Fallback: land the machine +
  compiler + *per-leaf* step-equality first; the whole-query composition can
  ship as the paper's "in progress" only if truly necessary (it should not
  be).
- **Constant-shrink regressions** (B1): touches the cost accounting spine;
  gate behind the existing 118/196727 theorems so any regression is caught by
  the theorem surface itself.
- **Scope creep:** the general BP tree-navigation library and other spokes are
  explicitly OUT of this plan; they resume after M3.

## 5. Why this beats plain extraction

Coq-style extraction introduces a trusted translation to OCaml. Here the
theorems already constrain computable Lean definitions, and Lean 4 compiles
them natively: the benchmark binary *is* the formal object, modulo the Lean
compiler — the same class of trust as the extraction step, with one fewer
moving part and an exact precedent in checked-code-as-`lake exe` practice.
Adding the verified reference machine (A3) then covers the remaining
"bespoke model" objection with the strongest known pattern: a standard
small-step semantics, a proved simulation, and an executable that referees can
run. Together with B1's small constants, every previously brainpower-consuming
element of the cost story becomes a pattern a reviewer has seen before.
