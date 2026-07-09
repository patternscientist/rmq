# RMQ Final Roadmap

This is the internal delegation roadmap for making the RMQ spoke as strong,
elegant, and reviewer-legible as possible. It is not a claim document. Public
claims remain governed by the theorem map, artifact claims, and paper-facing
docs.

The goal is to minimize places where a reviewer has to audit a bespoke
justification instead of recognizing a familiar formal-methods pattern:

- a narrow paper root with exact theorem aliases;
- a list-facing, classical RMQ statement;
- explicit separation between payload bits, proof-only fields, model-cost ticks,
  Lean runtime, and external executable behavior;
- checked model adequacy for the execution story;
- a reproducible artifact path with named commands and expected outputs;
- source architecture that makes the proof idea look inevitable rather than
  patched together.

## Success Standard

The RMQ spoke is paper-level when a skeptical reviewer can answer these
questions without reverse-engineering the repository:

1. What is the final theorem, and where is it checked?
2. What is counted as payload, and what is proof-only scaffolding?
3. What does the cost model count, and why is the trace not forgeable?
4. Which executable path, if any, is being claimed, and which theorem connects it
   to the model?
5. Which files are part of the paper root, and which files are broader checked
   library work, history, experiments, or future spokes?
6. Which design decisions were made deliberately, and why were nearby
   alternatives rejected?

For this roadmap, "elegant" means:

- public theorem statements use stable, mathematical concepts rather than stale
  compatibility thresholds;
- small/large or fast/slow regimes exist only when the formal object itself
  genuinely has regimes;
- constants are either clean and explained, or hidden behind a theorem that lets
  the paper state the asymptotic result without distracting arithmetic;
- helpers are named for the role they play in the final argument;
- refactors improve semantic boundaries without changing public theorem meaning.

## Current Fixed Point

The current integrated branch has a strong paper base:

- `RMQPaper` is the narrow reviewer import root.
- `RMQ.Headlines.RMQ` exposes the RMQ headline theorem surface.
- The list-facing final theorem gives the `2n + o(n)` succinct RMQ profile with
  constant query cost.
- The final execution story includes flat payload backing, successful-read
  counted-payload coverage, and no synthetic trace events.
- Supplied-store and footprint adequacy exist at the final shape/model layer.
- The public cost story distinguishes all-size and fast-regime constants.
- Artifact and paper-shell docs explain the theorem map and reproduction path.

The remaining pressure points are not "honesty" problems. They are places where
the artifact can be made cleaner and more familiar:

- The supplied-store/footprint story has now been lifted to the list-facing
  `SuccinctClassic` interface.
- The public all-size cost alias now uses the route-split theorem and fixed
  constant `4144`; exact all-size `118` remains false for the current
  zero-block structural replay.
- A zero-block guard and conservative footprint bounds remain visible enough to
  invite reviewer questions.
- Some implementation files are large enough that proof architecture is harder
  to see than it should be.
- The executable evidence is currently validation-oriented, not yet a
  reviewer-grade "this code path is the one the theorem talks about" story.

## Roadmap Ladder

Each rung is intended to be independently delegable. Do not skip a proof rung by
adding prose caveats. If a target is impossible or mis-specified, the worker
should produce a precise formal obstruction and a revised theorem target.

### R0. Canonicalize Process And Internal Plans

Status: this branch.

Deliverables:

- This roadmap.
- Design-decision entries for the roadmap choices.
- A concrete ADD tooling plan and first-pass implementation: coordinator/audit
  skills, prompt templates, claim-drift policy, advisory scripts, CI hooks, and
  issue/PR templates.
- Internal links from `AGENTS.md` and `docs/internal/README.md`.

Acceptance:

- `git diff --check`
- Targeted claim-drift scans over internal docs.

### R1. Lift Final Model Adequacy To The List-Facing Interface

Purpose: make the public theorem surface say, directly, that the classical
`List Int` RMQ query can be run against a supplied store that agrees on the
checked footprint, with the same result and bounded model cost.

Likely write scope:

- `RMQ/Core/SuccinctRMQClassic.lean`
- `RMQ/Headlines/RMQ.lean`
- paper theorem-map docs after the theorem lands

Likely theorem/interface targets:

- `SuccinctClassic.queryCostedWithStore`
- `SuccinctClassic.storesAgreeOnFootprint`
- `SuccinctClassic.queryCostedWithStore_eq_queryCosted_of_footprint`
- `SuccinctClassic.listIntFinalFullModelSoundnessExactOfFootprintGlobal`
- `SuccinctClassic.listIntFinalFullModelCostLeOfFootprintGlobal`
- `SuccinctClassic.listIntFastRegimeFinalFullModelCostLeOfFootprintGlobal`

Naming may change to match the local style, but the endpoint should be a public
alias under `RMQ.Headlines.RMQ` that consumes the existing final
shape/model-level supplied-store theorem rather than reproving the machinery.

Acceptance:

- The list-facing theorem has explicit hypotheses for the supplied store and
  footprint agreement.
- The theorem distinguishes value result, trace/model cost, and payload/store
  assumptions.
- `lake build RMQPaper`
- `lake build RMQ.Core.SuccinctRMQClassic`
- headline axiom checks and hygiene scans.

First worker prompt:

> Work in a fresh branch from the integrated RMQ paper branch. Goal: lift the
> final supplied-store/footprint adequacy theorem from the shape/final model
> layer to the public `SuccinctClassic` list-facing interface. Add the smallest
> clean list-facing wrapper needed for a caller to supply a store that agrees
> on the checked final footprint, and prove that the result and model cost agree
> with the canonical `queryCosted` path. Expose a stable alias in
> `RMQ/Headlines/RMQ.lean`. Do not weaken the existing flat-payload or
> no-synthetic story, and do not conflate Lean runtime with model cost. Run
> `lake build RMQPaper`, `lake build RMQ.Core.SuccinctRMQClassic`, headline
> axiom checks, hygiene scans, and `git diff --check`. Report theorem names,
> exact hypotheses, and what this now lets the paper claim.

### R2. Replace The Ugly All-Size Cost Surface With A Cleaner Theorem

Purpose: keep the correct all-size story but reduce or hide the distracting
`196727` constant behind a principled theorem surface.

Preferred endpoint:

- A clean all-size theorem whose public constant is the same as, or close to,
  the fast-regime constant.
- If exact all-size `118` is not possible, a theorem that derives a small named
  constant from a uniform table/route abstraction rather than a visible pile of
  compatibility leftovers.

Constraints:

- No uncounted dense answer tables.
- No proof-only fields that contain answers.
- No synthetic trace events.
- All successful reads remain backed by counted payload.
- The public route should not rely on `2^128`; that number may remain only as a
  compatibility lemma if still needed.

Likely write scope:

- `RMQ/Core/SuccinctClose/RelativeRmmMacro/*`
- `RMQ/Core/SuccinctFinal*.lean`
- `RMQ/Core/SuccinctRMQClassic.lean`
- headline/docs updates after the theorem lands

Acceptance:

- The old all-size theorem remains available as a compatibility alias if useful.
- The paper root exposes the cleaner all-size theorem.
- The proof explains, in names and local comments only where useful, why the
  small-size path is not hiding an answer table.
- Full RMQ build and artifact validation pass.

Second worker prompt:

> Work in a fresh branch from the integrated RMQ paper branch after the
> list-facing footprint lift has landed. Goal: replace the public all-size cost
> surface around `196727` with the cleanest theorem that is actually true. Start
> by tracing where the all-size constant is introduced and what remains of the
> zero-block/small-size compatibility path. Then prove a cleaner all-size cost
> theorem without adding uncounted dense answer tables, proof-only answer
> fields, synthetic events, or `2^128` public-route assumptions. Preserve
> compatibility aliases as needed, but make the reviewer-facing alias the new
> clean theorem. If exact fast-regime `118` all-size is formally impossible,
> produce a precise obstruction and the smallest principled constant theorem.
> Run full RMQ builds, headline axiom checks, hygiene scans, artifact validation,
> and `git diff --check`.

### R3. Retire Remaining Model Blemishes

Purpose: remove small proof artifacts that are correct but invite unnecessary
questions.

Targets:

- Remove or internalize the zero-block guard if a supplied-store equality theorem
  can make it unnecessary at the public level.
- Replace conservative "safe footprint" bounds with an exact dynamic read-set
  theorem if the proof cost is reasonable.
- Push word-width and bounded-address side conditions into named local
  well-formedness predicates consumed by the headline theorem.

Acceptance:

- The public theorem surface gets shorter or more conceptual.
- Any remaining guard is named as a real machine precondition, not a proof
  workaround.
- `docs/PAPER_MODEL_ADEQUACY.md` and theorem-map docs stay synchronized.

### R4. Refactor For Reviewer-Grade Architecture

Purpose: make the code look like a formalization a domain expert would choose,
not like an accumulation of successful patches.

This should happen after R1 and preferably after R2, because the refactor should
serve stable theorem boundaries.

Candidate splits:

- `SuccinctFinalRAM.lean` into payload layout, trace execution, cost bounds, flat
  payload backing, and final execution-story surfaces.
- `SuccinctFinalStoreParam.lean` into read-store abstraction, footprint
  agreement, supplied-store adequacy, and public compatibility aliases.
- `RelativeSummary.lean` into readiness predicates, route construction, budget
  facts, and old compatibility lemmas.

Rules:

- Keep public names stable through aliases.
- Rename only when the new name explains the final argument better.
- Do not mix semantic strengthening with mechanical file movement unless the
  strengthening is tiny and separately documented.
- Quarantine history, obstruction, proposal, and broad-spoke modules away from
  `RMQPaper`.

Acceptance:

- `import RMQPaper` remains narrow.
- File names and theorem groups line up with the paper proof outline.
- `docs/RMQ_IMPORT_CLOSURE.md` is regenerated.
- Full build and artifact gates pass.

### R5. Build The Executable Lean Artifact Path

Purpose: give reviewers a runnable path for the exact definitions adjacent to
the theorem, while keeping runtime evidence separate from model-cost claims.

Targets:

- A `lake exe` that builds payloads and runs `queryCosted` on deterministic
  fixtures.
- Differential checks against the reference `List Int` semantics.
- Trace checks for cost bounds, no-synthetic events, and payload read coverage.
- A benchmark mode that reports wall-clock construction/query times separately
  from model ticks.

Preferred executable name:

- `rmq_trace_validate` or `rmq_succinct_trace_validate`

Acceptance:

- `artifact/README.md` gives one reviewer command.
- CI stores logs/timings as workflow artifacts.
- Benchmarks do not become theorem claims.
- The executable path uses theorem-adjacent definitions, not a separate
  unchecked implementation.

### R6. Add A Verified Reference Word-RAM Machine

Purpose: make the trace/cost story pattern-match with formal-methods precedent:
a small-step machine, a first-order controller, and a simulation theorem.

Targets:

- A minimal Word-RAM reference machine with roughly the instruction set already
  needed by the query controller.
- A compiler or elaborator from the existing first-order/register program to
  that machine.
- A theorem that machine execution steps correspond to the existing trace cost,
  with result agreement.

This is the strongest next cost-story move before any C/Rust generation. It
does not replace the current model; it gives reviewers a familiar bridge.

Acceptance:

- The theorem is phrased as simulation/refinement, not as a claim about Lean
  runtime.
- The machine is small enough to audit.
- `RMQPaper` imports only the final alias, not exploratory machine experiments.

### R7. Translation-Validated External Code, If Still Needed

Purpose: provide a conventional compiled-code story only after the reference
machine exists.

Targets:

- A small C or Rust generator from the first-order Word-RAM query language.
- Translation-validation certificates checked in Lean.
- Deterministic CI builds and executable tests.

Defer:

- A fully verified backend/compiler.
- Whole-program performance claims beyond measured artifact evidence.

### R8. Paper And Artifact Freeze

Purpose: make the repository ready for a real submission process.

Targets:

- Citation-grade related work and novelty search log.
- Updated theorem correspondence table.
- Linux artifact timings.
- DOI-ready artifact bundle.
- Anonymous artifact variant if needed by the venue.
- Final external audit packet.

Venue alignment:

- CPP explicitly values design choices, rejected alternatives, proof-assistant
  feedback, formal models of computation, certified algorithms, and complexity
  proofs.
- ACM artifact criteria reward documentation, completeness, exercisability, and
  reusability.
- The Affeldt et al. succinct-data-structure precedent makes rank/select/RMQ
  and executable formalization evidence legible, but novelty language still
  needs a referee-grade literature pass.

## What Not To Work On Next

- Do not start C/Rust generation before the list-facing final-model lift and the
  reference-machine plan are settled.
- Do not spend proof effort on union-find, broad BP navigation, or non-RMQ
  spokes until the RMQ paper path is frozen.
- Do not add more prose caveats as a substitute for theorem-shaped cleanup.
- Do not import Mathlib or broaden the trust base.
- Do not use raw private chat transcripts or hidden model reasoning as public
  proof evidence.
- Do not rename public theorem surfaces without aliases and a theorem-map
  update.

## Verification Gates

Typical proof branch:

```powershell
lake build RMQPaper
lake build RMQ
lake build RMQExamples
lake env lean scripts/axiom_check.lean
lake env lean scripts/wordram_axiom_check.lean
lake env lean scripts/headline_axiom_check.lean
rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ RMQExamples lakefile.toml
rg -n "native_decide|Lean\.ofReduceBool" RMQ RMQExamples
git diff --check
```

Typical docs/process branch:

```powershell
git diff --check
rg -n "first mechanized|first-ever|cannot be forged|artifact ready|AE-ready|Lean runtime|2\^128|196727|118" README.md artifact docs
```

## Research Basis

- CPP 2026 call for papers:
  <https://popl26.sigplan.org/home/CPP-2026>
- ACM artifact review and badging:
  <https://www.acm.org/publications/policies/artifact-review-and-badging-current>
- Affeldt et al., "A formalization of succinct data structures in Coq":
  <https://arxiv.org/abs/1904.02809>
- Codex documentation:
  <https://developers.openai.com/codex/>
- Introducing Codex:
  <https://openai.com/index/introducing-codex/>
- GitHub Actions documentation:
  <https://docs.github.com/en/actions>
