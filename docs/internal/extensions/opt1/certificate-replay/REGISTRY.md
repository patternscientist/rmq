# OPT-1 certificate replay registry

Version: `opt1-certificate-replay-v3`. Exactly 80 cases: 78 rejects and two accepts.
The independent runner literals and this table must agree with all 39 names
in the root-owned `FIELDS.json` version `opt1-certificate-fields-v3`.

| Delete case | Weaken case | Field |
| --- | --- | --- |
| D01-allocationResidualLittleO | W01-allocationResidualLittleO | allocationResidualLittleO |
| D02-completeResidualLittleO | W02-completeResidualLittleO | completeResidualLittleO |
| D03-widthBounds | W03-widthBounds | widthBounds |
| D04-dataCapacity | W04-dataCapacity | dataCapacity |
| D05-completeCapacity | W05-completeCapacity | completeCapacity |
| D06-memoryWordsFit | W06-memoryWordsFit | memoryWordsFit |
| D07-allocationAddressesFit | W07-allocationAddressesFit | allocationAddressesFit |
| D08-programFieldsFit | W08-programFieldsFit | programFieldsFit |
| D09-budgetExact | W09-budgetExact | budgetExact |
| D10-programLength | W10-programLength | programLength |
| D11-encodedProgramLength | W11-encodedProgramLength | encodedProgramLength |
| D12-programReduction | W12-programReduction | programReduction |
| D13-emittedProgram | W13-emittedProgram | emittedProgram |
| D14-originalExecutionBound | W14-originalExecutionBound | originalExecutionBound |
| D15-originalReducedFuel | W15-originalReducedFuel | originalReducedFuel |
| D16-arbitraryMemoryObservations | W16-arbitraryMemoryObservations | arbitraryMemoryObservations |
| D17-completedExecution | W17-completedExecution | completedExecution |
| D18-adequateFuel | W18-adequateFuel | adequateFuel |
| D19-registerCount | W19-registerCount | registerCount |
| D20-scratchCount | W20-scratchCount | scratchCount |
| D21-unusedRegisters | W21-unusedRegisters | unusedRegisters |
| D22-validInputs | W22-validInputs | validInputs |
| D23-natContract | W23-natContract | natContract |
| D24-leftmost | W24-leftmost | leftmost |
| D25-result | W25-result | result |
| D26-halt | W26-halt | halt |
| D27-invalidGuard | W27-invalidGuard | invalidGuard |
| D28-stepBound | W28-stepBound | stepBound |
| D29-categoryPartition | W29-categoryPartition | categoryPartition |
| D30-finalStateFit | W30-finalStateFit | finalStateFit |
| D31-transitionSafety | W31-transitionSafety | transitionSafety |
| D32-prefixSafety | W32-prefixSafety | prefixSafety |
| D33-readWidth | W33-readWidth | readWidth |
| D34-positionalReadBacking | W34-positionalReadBacking | positionalReadBacking |
| D35-orderedLogicalRefinement | W35-orderedLogicalRefinement | orderedLogicalRefinement |
| D36-logicalReadOnly | W36-logicalReadOnly | logicalReadOnly |
| D37-suppliedMemoryAgreement | W37-suppliedMemoryAgreement | suppliedMemoryAgreement |
| D38-specResult | W38-specResult | specResult |
| D39-noFailedLoads | W39-noFailedLoads | noFailedLoads |

The full order is A01-UNCHANGED, A02-COMMENT, then each row's D followed by W.
Both A cases expect ACCEPT from Certificate, Capstone and unchanged Consumers.
A02 adds only a trailing Lean comment to the isolated Certificate source.
Each D case removes the field and matching Capstone initializer. Each W case
replaces the complete field proposition by `True` and matching initializer by
`True.intro`. Both changed producer modules must compile with exit zero.
The fixed consumer must then fail with a located `invalid field` (D) or
`type mismatch` (W) diagnostic inside that field's `_expectedType` theorem,
and with no recognized located Lean error headers outside the exact theorem.
A producer failure, unrecognized located error kind, timeout or known
setup/resource failure is not an expected reject.
An additional column-zero `error:` or `uncaught exception:` line also rejects
the compile-time result even when a valid selected-field diagnostic is present;
indented diagnostic detail may contain quoted `error:` text.
This recognizes ordinary located Lean error headers, unlocated top-level
`error:`/`uncaught exception:` headers and the pinned known resource-failure
patterns; it does not claim to classify arbitrary diagnostic prose.

Every fixed consumer type is compared with the unmutated root FIELDS.json;
both `_expectedType` and `_canonical` theorem bodies are pinned. Types are
never extracted from a mutant. The consumer copy is byte-identical in every
case, including both expected accepts.

`-PrepareOnly` applies and restores all selected isolated-copy mutations
without invoking Lean. `-OnlyCase` selects exactly one of these 80 IDs;
omission selects the full registry. Empty, whitespace, malformed, unknown
and duplicate parameters must fail at the actual script boundary. Separate
registry and selector self-test modes perform no semantic execution.

The import provenance contract is pinned to the successful runtime receipt
`runtime-replay/evidence/full-runtime.json`, source commit
`ac5af8e416f906391dc117f083a883acc053a268`, raw SHA-256
`a7eb5831a88a7431607d5fe1d7189318d41978391e0a10be3ed336c014563661`.
Its exact checked import inventory and source/artifact hashes are the expected
values. Live timestamps are an additional freshness check, not evidence by
themselves that source and object files correspond.

Each campaign copies the 259 immutable prerequisite objects once into a
private read-only snapshot. Each case gets the complete `RMQ` hierarchy using
hardlinks to that snapshot; it never links to the main task cache.
Certificate, Capstone and Consumers object paths are excluded. Producer
output paths must be absent before compilation and regular private files
afterward. `LEAN_PATH` contains only the complete case library; installed
Lean/Std imports use Lean's normal toolchain search. Snapshot and original
cache hashes are checked after the campaign. `-LibrarySelfTestOnly` exercises
real links, private outputs, alias/path/provenance rejection and hash
preservation without launching Lean.
