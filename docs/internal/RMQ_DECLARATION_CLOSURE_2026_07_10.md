# RMQ Declaration Closure - 2026-07-10

Status: internal F0 evidence.
Pinned source frontier: `25395d43deea39cdbac2c273c60d1298c93cc2f3`.

This report records the durable coordinator synthesis of the W11 dependency
scout. It is process and architecture evidence, not a theorem or public artifact
claim.

## Method

The scout compiled temporary Lean environment probes against `RMQPaper` and
the two executable validation roots.

For each root declaration it computed:

- type closure: constants reachable from `ConstantInfo.type`;
- full closure: constants reachable from types and proof/value bodies, including
  opaque theorem bodies;
- body-only closure: full closure minus type closure;
- declaration-to-module attribution through the Lean environment.

Lean/Std declarations were counted as terminal leaves but not recursively
expanded. That keeps the recursive closure scoped to workspace declarations.

A source import parser independently computed workspace module closure. The
analysis compared public declaration closure with module import closure and
checked executable roots in separate environments because both executable
modules export global `main`.

## Results

At the pinned commit:

- `RMQPaper` imports 126 workspace Lean modules.
- Those modules contain 105,607 nonblank Lean lines and 111,928 physical lines.
- `RMQ.Headlines.RMQ` contributes 57 public root declarations.
- Their aggregate type/body closure reaches 4,194 workspace declarations across
  72 source modules.
- Fifty-four of the 126 imported modules contribute no declaration to any
  headline type or proof/value body.
- The five mandatory headline targets reach 67 source modules.
- The validator and cost harness each add only their own validation module
  beyond the paper module set; their actual closures are subsets of the paper
  dependencies plus that root.
- Eleven declaration-free compatibility/barrel modules occur in the paper
  import DAG and dominate 35 non-barrel descendants.

The five target roots were:

- `listIntSuccinctRMQPaperMainTheorem`;
- `listIntSuccinctRMQFlatPayloadStoreNoSyntheticExecutionStory`;
- `listIntSuccinctRMQFinalFullModelSoundnessExactOfFootprintGlobal`;
- `listIntSuccinctRMQFinalFullModelCostLeOfFootprintGlobal`;
- `succinctRMQWholeQueryGlobalWordTraceCostedCostLe`.

The first two have the same closure because both consume
`listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story`.

## Interpretation

The paper root is narrow at its public entry point, but the internal import DAG
is materially wider than the declarations used by its public theorem bodies.
This supports exact-import experiments and later quarantine work.

It does not prove that the 54 modules are globally dead:

- other public spokes may consume them;
- source elaboration can require notation, instances, attributes, tactics, or
  simp lemmas that do not survive as named constants in an elaborated body;
- proof erasure and compiled runtime reachability are different analyses;
- a module can be intentionally retained as a compatibility root.

No module should be deleted from this result alone.

## Accepted A1 Candidates

After U2 stabilizes the route:

- test exact internal imports while retaining the eleven barrels as re-export
  compatibility roots;
- narrow broad `SuccinctSpace`, `TwoLevel`, `BuiltRouting`, endpoint,
  prefix-range, and relative-rmM imports by checked compilation experiments;
- keep `SuccinctFinalRAM` as a compatibility facade while splitting only
  stable proof units;
- keep `RMQPaper` as the reviewer root even though it is declaration-free;
- preserve lower-bound imports required by the all-headline union;
- run a broad-repository reverse-consumer scan before quarantine or deletion.

## Evidence Needed Before Removal

A1 removal/quarantine requires all of:

1. no consumer in the full repository declaration reverse graph;
2. a successful exact-import replacement and `lake build RMQPaper`;
3. full `lake build` and public axiom checks;
4. regenerated import-closure counts;
5. an explicit compatibility/public-alias disposition;
6. a design-decision entry for any removed public or historical surface.

## Reproducibility Status

The scout's temporary Lean probes and TSV outputs were generated outside the
repository and used hard-coded local output paths. Their methodology and
results were independently inspected, but those temporary files are not part
of the public artifact. A discarded PowerShell import analyzer had malformed
whitespace regular expressions and is not accepted evidence; the counts above
come from the Lean-generated TSVs and the inspected Python import analyzer.

A later tooling branch should productionize the probe by:

- accepting roots and output paths as arguments;
- emitting deterministic JSON/TSV;
- recording Lean/toolchain and target commit;
- checking both declaration closure and global reverse consumers;
- running as an advisory CI/import-architecture job.

Until then, the numbers in this document are internal planning evidence. The
existing checked import-closure report remains the public module-level source.

## F0 Disposition

F0 is complete for U1 planning: the total-layout work is confirmed to sit on the
real body dependency path and must preserve stable aliases through
`RelativeSummary`, directory/RAM, final store, and list-facing consumers.

F0 is not a deletion license. The global reverse-consumer and checked
import-pruning work remains an A1 prerequisite.

The temporary W11 detached worktree remains a lifecycle cleanup item; it should
be removed only after confirming it is clean and preserving this synthesis.
