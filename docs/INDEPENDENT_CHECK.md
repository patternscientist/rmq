# Independent Kernel Re-Checking (advisory)

This document describes how a reviewer can re-check this development with a
kernel implementation **other than** Lean's own, and states plainly what this
project has and has not done.

**Status: a scoped V1 advisory trial ran on 2026-10-01 and failed. No
independent kernel acceptance is claimed.** Read §4 for the exact scope, tool
identities and outcome.

## 1. Why this is advisory and not a gate

The project's trust base is the Lean 4 kernel under the pinned toolchain in
`lean-toolchain`, plus the standard axioms checked by `scripts/axiom_check.lean`
and its siblings. An independent checker does not replace that; it reduces
reliance on a single kernel implementation being correct.

`docs/internal/ADD_WORKFLOW_TOOLING_PLAN.md` already scopes this as
"advisory/nightly `nanoda` checking, distinct from the kernel gate", and
forbids broadening the project's Lake dependency graph for tooling. The V1
freeze requirement also calls for an advisory independent-checker run. This
document keeps its outcome separate from the required Lean checks.

## 2. Why the checker tools are built out of tree

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

The following is an outline, not a claim that current upstream tips compile
unchanged against Lean 4.22.0. Build tools in a scratch directory outside the
repository, with a compatible exporter revision and the same toolchain version
as `lean-toolchain`. The exact V1 trial revisions and exporter API patch are
recorded in §4.

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

- The V1 base `ee44f04a561f2194b3713f071c26b6faf9ba7fab` has 262 local Lean
  modules in the `RMQPaper` closure, enumerated in
  `internal/v1/source-closure-inventory.json`. Export size and check time scale
  with the elaborated environment, not the source-file count. The V1 trial
  below exported one specification theorem and its dependencies, not this full
  closure.
- The exporter and the checker must agree on the export format version. A
  mismatch presents as a parse failure, not as a proof failure. Do not report a
  format mismatch as a soundness finding.

## 4. What this project has actually done

The required Lean checks use the pinned Lean kernel and curated axiom
inventories. Their exact V1 command results are recorded separately; the
advisory checker does not replace them.

On 2026-10-01, the V1 work built an out-of-tree `lean4export` at
`e6c7eafbb83cfad518b196164ee977f7f0ba3701`, adapting its `Expr.updateLet!`
call to the Lean 4.22.0 API and preserving the let-expression flag. It built
`nanoda` at `e5438ac0a85a036b6dfe093aa457bc3448498014`. The compatible legacy
export format was used. The selective export contained
`RMQ.leftmostArgMin_unique`, its dependencies, and the complete `Eq`/`Quot`
package. The reference specification blob is unchanged from the V1 base.

The corrected input passed the earlier missing-Quot-declaration failure, then
the checker exited `101` at `src/tc.rs:806`, failing a definitional-equality
assertion on the omega-generated auxiliary declaration
`RMQ.leftmostArgMin_unique._proof_1_1`. Its cause was not established. This is
neither an independent acceptance of the selected theorem nor a demonstrated
Lean kernel defect. No theorem or axiom whitelist was changed to obtain a pass.

The [advisory record](internal/v1/NANODA_ADVISORY.json) preserves the tool
revisions, exact exporter patch, export arguments, checker configuration,
executable/export SHA256s and actual failure output. It is the reproducible
scope record for this trial. A complete `RMQPaper` or full-project independent
kernel check has not passed; Lean4Lean was not run.
