# LIFE-NATIVE-1: proposed startup source amendment

Status: PROPOSED; no protected source changed and no build performed.

The ordinary generated module-initialization route executes five concrete
proof-witness definitions before a lifecycle request. The proposed amendment
adds `@[macro_inline]` to exactly those five nonrecursive definitions in two
protected files. Their names, types, bodies and theorem propositions remain
unchanged. The accompanying `STARTUP_AMENDMENT.patch` is the concrete proposal,
not evidence that the amendment has been approved or applied.

This is necessary to avoid these five roots when using the ordinary generated
initializers and the current import graph. It is not a universal obstruction to
native lifecycle implementation. A custom generated-C initializer-pruning
transformation is an in-scope alternative in principle, but adds a trusted
transformation and its dependency-completeness obligations; it is not adopted.

## Identity and evidence level

- Worker: LIFE-NATIVE-1; read-only formal-inventory leaf.
- Checkout: `C:/Users/poin/.codex/worktrees/44d6/RMQ`.
- Base and inspected HEAD: `3dbdebedcc6ba6b2a864df0d46dcc09ccaaa7536`.
- Branch: `codex/life-native-1-consuming-owner`.
- Governance: `7b227c49ef2ec044b702126cc41c9add847eed01`; independent role preflight
  passed with `rmq-proof-sprint` required and actual runtime catalog
  `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`.
- Historical generated C: `C:/Users/poin/.codex/worktrees/e993/RMQ/.lake/build/ir`.
- Compiler source inspected locally:
  `C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/src/lean/Lean/Compiler`.

The historical C was read, not rebuilt or executed. Both affected source files,
and every source module supplying an edge in the chains below, match the current
checkout byte-for-byte. The C hashes identify the inspected artifacts, but do
not independently prove their compiler invocation, binary linkage, complete
cache provenance or behavior of a newly compiled candidate. This is source and
cached-artifact design evidence, not a fresh native-run result. No startup
duration, heap-capacity or reference-count-copy measurement is claimed.

| Exact path relative to repository or historical IR root | SHA256 |
| --- | --- |
| `RMQ/Core/SuccinctClose/EndpointFringe/InteriorCandidate/InteriorDirectory/SparseLevelWidth.lean` (current and e993) | `25a067e1c7e41c525680e44bb0767868eeeace8d09825f232cb957ee000996b1` |
| `RMQ/Core/SuccinctFinal/RAM/ReviewerReachabilitySmall.lean` (current and e993) | `0e0fe1e5f7e56104eb8007bff55b844b1ec9627f88f5cb519b0a8db625297a18` |
| `RMQ/Core/SuccinctClose/EndpointFringe/InteriorCandidate/InteriorDirectory/SparseLevelWidth.c` | `8d1bf03dc2a6df19ca52e8fcc8691e7b30d9e094df6472f8f8b3274b1894ca0b` |
| `RMQ/Core/SuccinctFinal/RAM/ReviewerReachabilitySmall.c` | `183be79d345cf7a493e194278f4ac1381f9bfc80f920a0b0e64aaff99e7df39f` |
| `RMQ/Core/WordRAM/Lifecycle/Executable.c` | `5a8e46003d9853ffb12d707401f89d47a3f9bcf91203853647df468eb51db024` |
| `RMQ/Core/WordRAM/Lifecycle/ArrayRun.c` | `45aa5cfbe2b34c81682f3c472cc5f28bf9d2c50bc99981de2c349bbdcfa6928b` |

## Exact five-definition scope

Line numbers refer to the unmodified base source and inspected historical C.

| Source module | Source line and declaration | Actual historical initialization |
| --- | --- | --- |
| `SparseLevelWidth.lean` | 1603: `canonicalRelativeRmmInteriorCost33WitnessShape` | C 857-864 constructs `canonicalRelativeRmmInteriorCost33RightSpine 3469`; C 904-907 initializes and marks the result persistent. |
| `SparseLevelWidth.lean` | 1607: `canonicalRelativeRmmInteriorCost33WitnessInput` | C 874-881 calls `CartesianShape.representative` on that shape; C 908-911 initializes and marks the result persistent. |
| `ReviewerReachabilitySmall.lean` | 1712: private `reviewerSingletonBeforeLCAState` | C 648-659 invokes `WholeQueryProgram_evalGlobalWordTrace`; C 1063-1068 initializes the closed helper and retained state. |
| `ReviewerReachabilitySmall.lean` | 1733: private `reviewerSingletonBeforeRankState` | C 732-743 invokes `WholeQueryProgram_evalGlobalWordTrace`; C 1079-1082 initializes the helper and retained state. |
| `ReviewerReachabilitySmall.lean` | 2042: private `reviewerIncreasingSixteenBeforeLCAState` | C 815-826 invokes `WholeQueryProgram_evalGlobalWordTrace`; C 1085-1090 initializes the helper and retained state. |

The two full source paths are given in the hash table. The three state
definitions evaluate concrete reference programs on singleton or sixteen-value
inputs; they are not part of `runOwner`, `initialOwner`, the fixed lifecycle
program or the service evaluator. The spine/input definitions support a
concrete cost witness. Proof erasure alone does not erase these values because
their types are computational data types.

## Complete witnessed import chains

Each row identifies a source import and the matching live import-initializer
call in the importing module's historical C. The prefix is shared by both
targets. All paths below are Lean module names; replace dots with slashes and
append `.lean` or `.c` under the appropriate root.

| Importing module | Imported module | Historical importing C line |
| --- | --- | --- |
| `RMQ.Core.WordRAM.Lifecycle.Executable` | `RMQ.Core.WordRAM.Lifecycle.Input` | 1239 |
| `RMQ.Core.WordRAM.Lifecycle.Input` | `RMQ.Core.WordRAM.Lifecycle.Builder` | 660 |
| `RMQ.Core.WordRAM.Lifecycle.Builder` | `RMQ.Core.WordRAM.Packed.Width` | 332 |
| `RMQ.Core.WordRAM.Packed.Width` | `RMQ.Core.WordRAM.Packed.Allocation` | 190 |
| `RMQ.Core.WordRAM.Packed.Allocation` | `RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerControllerProof` | 1022 |
| `RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerControllerProof` | `RMQ.Core.SuccinctRMQClassic` | 6678 |

The complete remaining suffix to the three concrete reference-state roots is:

| Importing module | Imported module | Historical importing C line |
| --- | --- | --- |
| `RMQ.Core.SuccinctRMQClassic` | `RMQ.Core.SuccinctFinal.RAM.ReviewerReachabilitySmall` | 1039 |

The complete remaining suffix to the shape/input roots is:

| Importing module | Imported module | Historical importing C line |
| --- | --- | --- |
| `RMQ.Core.SuccinctRMQClassic` | `RMQ.Core.SuccinctFinalModelAdequacy` | 1036 |
| `RMQ.Core.SuccinctFinalModelAdequacy` | `RMQ.Core.SuccinctFinalStoreParam` | 30 |
| `RMQ.Core.SuccinctFinalStoreParam` | `RMQ.Core.SuccinctClose.RelativeRmmMacro.ConcreteDirectoryRAMStoreParam` | 1528 |
| `RMQ.Core.SuccinctClose.RelativeRmmMacro.ConcreteDirectoryRAMStoreParam` | `RMQ.Core.SuccinctClose.RelativeRmmMacro.ConcreteDirectoryRAM` | 3086 |
| `RMQ.Core.SuccinctClose.RelativeRmmMacro.ConcreteDirectoryRAM` | `RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorRAM` | 3128 |
| `RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorRAM` | `RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorDirectory` | 3198 |
| `RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorDirectory` | `RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorDirectory.ValueDependency` | 26 |
| `RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorDirectory.ValueDependency` | `RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorDirectory.SparseLevelWidth` | 408 |

Every listed C call has the form
`res = initialize_<imported_module>(builtin, lean_io_mk_world());` inside its
module initializer. These are live initialization calls, not just declarations
or linker inventory entries.

## Named-symbol scan of all 355 generated modules

The recursive RMQ source import closure rooted at
`RMQ.Core.WordRAM.Lifecycle.Executable` has 355 modules. All 355 corresponding
historical `.c` files exist; missing count is zero. Each of the five exact
declaration-name strings was searched in every file. Results:

| Exact searched declaration-name string | Matching generated modules | Matches outside defining module |
| --- | --- | --- |
| `canonicalRelativeRmmInteriorCost33WitnessShape` | `SparseLevelWidth` only | 0 |
| `canonicalRelativeRmmInteriorCost33WitnessInput` | `SparseLevelWidth` only | 0 |
| `reviewerSingletonBeforeLCAState` | `ReviewerReachabilitySmall` only | 0 |
| `reviewerSingletonBeforeRankState` | `ReviewerReachabilitySmall` only | 0 |
| `reviewerIncreasingSixteenBeforeLCAState` | `ReviewerReachabilitySmall` only | 0 |

This checks named-symbol references in the actual cached C, including private
mangled names. It is not a universal semantic call-graph theorem and does not
prove that every possible closed constant is harmless. Direct initializer
inspection supplies the five positive execution witnesses above. Splitting the
new runtime/proof files alone is insufficient: the import union of existing
`ArrayRun`, `Input` and `Program` still has 346 RMQ modules and reaches both roots.

## Compiler-supported mechanism and rejected alternatives

Pinned Lean 4.22 compiler source provides the following evidence:

- `LCNF/Main.lean:24-43`, `shouldGenerateCode`, documents and implements
  `if hasMacroInlineAttribute env declName then return false`.
- `InlineAttrs.lean:19-31,43-53,63-68` accepts the attribute on nonrecursive
  definitions and expands uses before compilation. All five proposed targets
  are nonrecursive definitions; none changes its logical body or type.
- `IR/EmitC.lean:710-738`, `emitDeclInit`, initializes every generated
  zero-parameter declaration; `:740-755`, `emitInitFn`, calls every import
  initializer and emits the declaration initializers.
- `LCNF/ExtractClosed.lean:148-157` shows that
  `compiler.extract_closed=false` only skips closed-subterm extraction. It does
  not exclude an existing ordinary zero-parameter definition from code generation.

| Compiler file relative to the inspected compiler root | SHA256 |
| --- | --- |
| `LCNF/Main.lean` | `c4d11544ae069c32c55cc87b07da5456d2d0dbc8742c01ff3ce89cf605c33cf6` |
| `InlineAttrs.lean` | `14e41fb36870999e6bbb7b2d3224d83ed92c3f24a4a08c13a7e8cbd3f89ec77a` |
| `IR/EmitC.lean` | `b52a02df496b2b64071cbdfbe798900f4d04e1f80558207ad6675dc332c84523` |
| `LCNF/ExtractClosed.lean` | `2305bd463fb06f4e5b33c66c42819567e013045eaf203140cd52ed05e109bbbf` |

Adding an ignored Unit argument changes source signatures and all theorem
applications, and would still require checking closed-subterm extraction.
`@[inline]` alone does not suppress code generation: `shouldGenerateCode` says
ordinary inline declarations still receive code. The five `@[macro_inline]`
annotations are therefore the narrower proposal. Annotating names only after
import in a new module cannot remove the already generated defining modules'
initializers.

If scope is amended, perform a fresh governed compilation of both changed
sources and affected consumers; inspect their emitted initializers and all new
runtime closure references; confirm the five values are not reintroduced by
inlining into another computational constant; and run a bounded actual startup.
The startup change does not replace the remaining lifecycle export, ownership,
capacity, failure, codec, replay or full-consumer obligations. Historical
producer byte identities must remain recorded separately from the amended
source and resulting artifacts. DD/WDD entries and final certification belong
to the main worker after authorization and implementation.

Proposal validation: `git apply --check
docs/internal/extensions/lifecycle-native1/STARTUP_AMENDMENT.patch` passed with
exit 0 against the unchanged protected source. The patch adds exactly five
attribute lines and changes no existing source line. Both new artifacts passed
strict UTF-8 decoding and direct trailing-whitespace checks. Path-focused Git
status showed only these two new untracked artifacts and no changes to either
protected source; this leaf did not stage or commit. Fresh compilation and
startup validation are deliberately still pending authorization.
