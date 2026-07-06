# AI-Assisted Development Note

AI assistance was used to help navigate the codebase, propose proof scripts,
and draft documentation. The trust story for the artifact does not rest on AI
authorship.

The trust base is:

- Lean kernel checking of the committed theorem statements and proofs.
- A reproducible build pinned by `lean-toolchain`.
- Curated axiom checks in `scripts/headline_axiom_check.lean`,
  `scripts/wordram_axiom_check.lean`, and `scripts/axiom_check.lean`.
- A public theorem map connecting paper claims to checked Lean names.
- Public artifact scripts, especially `scripts/reproduce_artifact.sh`, that run
  the build, axiom checks, forbidden-token scans, and whitespace diff check.

Reviewers should treat the Lean files and reproduction logs as the artifact.
The prose documents are maps to the checked theorem surfaces, not replacements
for kernel checking.
