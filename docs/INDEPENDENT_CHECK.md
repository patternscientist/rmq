# Independent Kernel Re-Checking (advisory)

This document describes how a reviewer can re-check this development with a
kernel implementation **other than** Lean's own, and states plainly what this
project has and has not done.

**Status: procedure documented, NOT executed by this project.** Read §4 before
citing this document as evidence of anything.

## 1. Why this is advisory and not a gate

The project's trust base is the Lean 4 kernel under the pinned toolchain in
`lean-toolchain`, plus the standard axioms checked by `scripts/axiom_check.lean`
and its siblings. An independent checker does not replace that; it reduces
reliance on a single kernel implementation being correct.

`docs/internal/ADD_WORKFLOW_TOOLING_PLAN.md` already scopes this as
"advisory/nightly `nanoda` checking, distinct from the kernel gate", and
forbids broadening the project's Lake dependency graph for tooling. The V1
freeze requirement is likewise worded "advisory independent checker **where
supported**". This document is written to that scope.

## 2. Why it cannot be run in-tree today

An external checker consumes an *export file*, not `.olean`s. Producing one
requires an exporter, and:

- **Lean 4.22.0 has no built-in exporter.** Verified on the pinned toolchain:
  `lean --help` lists no `--export` option. (Older Lean 4 versions did; it was
  moved out of the binary.)
- The exporter is therefore the separate `lean4export` project, which must be
  built against a matching toolchain **out of tree**. Adding it as a Lake
  dependency is explicitly disallowed by the tooling plan.

So the procedure below is deliberately out-of-tree and manual.

## 3. Procedure

Run from a scratch directory outside this repository, with the same toolchain
version as `lean-toolchain`.

```bash
# 1. build this project's oleans first, in the repo
lake build

# 2. out of tree, build an exporter matching the pinned toolchain
git clone https://github.com/leanprover/lean4export
cd lean4export
# set its lean-toolchain to match this project's, then
lake build

# 3. export a root module (RMQPaper is the narrow paper closure; RMQ is broader)
LEAN_PATH=<repo>/.lake/build/lib/lean \
  ./.lake/build/bin/lean4export RMQPaper > rmq_paper.export

# 4. check the export with an independent kernel
#    (a) nanoda, Rust:      https://github.com/ammkrn/nanoda_lib
#    (b) Lean4Lean, Lean:   an independent checker written in Lean itself
```

Two notes that will otherwise cost time:

- Export files for this repository are large. The `RMQPaper` closure is 153
  files and ~139k lines of Lean source (`docs/RMQ_IMPORT_CLOSURE.md`); export
  size and check time scale with the elaborated environment, not the source.
- The exporter and the checker must agree on the export format version. A
  mismatch presents as a parse failure, not as a proof failure. Do not report a
  format mismatch as a soundness finding.

## 4. What this project has actually done

- **Executed:** the Lean kernel checks every declaration under the pinned
  toolchain on every CI run, and `scripts/axiom_check.lean`,
  `scripts/headline_axiom_check.lean`, `scripts/wordram_axiom_check.lean`,
  `scripts/hub_axiom_check.lean` and `scripts/union_find_axiom_check.lean`
  confirm the axiom set of the cited declarations.
- **Not executed:** any independent-kernel re-check. No export file has been
  produced, and neither `nanoda` nor `Lean4Lean` has been run against this
  development.

Therefore: **this document is a procedure, not a result.** It must not be cited
as evidence that an independent kernel has confirmed anything here. If a
reviewer runs it, the outcome should be recorded in
`docs/internal/audit_reports/` with the exporter and checker commits pinned.
