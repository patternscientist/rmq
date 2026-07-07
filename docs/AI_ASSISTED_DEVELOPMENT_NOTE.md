# AI-Assisted Development Note

This project used heavy AI-assisted audit-driven development. AI agents helped
navigate the codebase, propose and repair proof scripts, draft documentation,
run theorem-inventory checks, and act as adversarial reviewers. The workflow
used high-context coordinators, scoped specialist workers, external audits, and
audit-of-audits synthesis to turn objections into theorem-shaped repair targets
or documentation patches.

The full process note is [`ADD_PROVENANCE.md`](ADD_PROVENANCE.md). This short
note is the trust boundary: AI assistance, ADD process records, worker reports,
audit summaries, and chat transcripts are provenance evidence, not proof
objects. The trust story for the artifact does not rest on AI authorship or on
the correctness of any agent.

The proof trust base is:

- Lean kernel checking of the committed theorem statements and proofs.
- A reproducible build pinned by `lean-toolchain`.

The reviewer and reproducibility checks around that trust base include:

- Curated axiom checks in `scripts/headline_axiom_check.lean`,
  `scripts/wordram_axiom_check.lean`, and `scripts/axiom_check.lean`.
- Hygiene scans for placeholders, custom axioms, unsafe hooks, and other known
  proof-bypass mechanisms.
- A public theorem map connecting paper claims to checked Lean names.
- Public artifact scripts, especially `scripts/reproduce_artifact.sh`, that run
  the build, axiom checks, forbidden-token scans, and whitespace diff check.
- Human/auditor review that the prose claim surface matches the checked theorem
  surface.

Reviewers should treat the Lean files and reproduction logs as the artifact.
The prose documents are maps to the checked theorem surfaces, not replacements
for kernel checking.
