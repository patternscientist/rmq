# Complete changed-file inventory

Compared with `3dbdebedcc6ba6b2a864df0d46dcc09ccaaa7536`: 95 changed or new paths.

The two predecessor Lean files contain only the five expressly approved
`macro_inline` insertions. Existing Cargo/lib glue and public entries are
additive; both decision ledgers preserve their original raw prefixes.
The report and external delivery receipt carry verification and final
commit identities. Raw transcripts, build artifacts and archives stay
in the ignored `.lake/lifecycle-native1/` evidence directories.

## Lean source and independent consumers (14)

- `RMQ/Core/SuccinctClose/EndpointFringe/InteriorCandidate/InteriorDirectory/SparseLevelWidth.lean`
- `RMQ/Core/SuccinctFinal/RAM/ReviewerReachabilitySmall.lean`
- `RMQ/Core/WordRAM/Native/Lifecycle.lean`
- `RMQ/Core/WordRAM/Native/Lifecycle/Admission.lean`
- `RMQ/Core/WordRAM/Native/Lifecycle/AdmissionContract.lean`
- `RMQ/Core/WordRAM/Native/Lifecycle/BoundaryProofs.lean`
- `RMQ/Core/WordRAM/Native/Lifecycle/Codec.lean`
- `RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean`
- `RMQ/Core/WordRAM/Native/Lifecycle/Entry.lean`
- `RMQ/Core/WordRAM/Native/Lifecycle/Observations.lean`
- `RMQ/Core/WordRAM/Native/Lifecycle/Repack.lean`
- `RMQ/Core/WordRAM/Native/Lifecycle/Run.lean`
- `RMQ/Core/WordRAM/Native/Lifecycle/ThinRun.lean`
- `RMQ/Validation/LifecycleNativeContract.lean`

## Native ABI, ownership facade and clients (11)

- `native/packed-rmq/Cargo.toml`
- `native/packed-rmq/README.md`
- `native/packed-rmq/examples/lifecycle.cpp`
- `native/packed-rmq/include/packed_rmq_lifecycle.h`
- `native/packed-rmq/lifecycle_shim.c`
- `native/packed-rmq/packed_rmq_lifecycle.def`
- `native/packed-rmq/src/lib.rs`
- `native/packed-rmq/src/lifecycle.rs`
- `native/packed-rmq/src/lifecycle_main.rs`
- `native/packed-rmq/tests/lifecycle_owner.c`
- `native/packed-rmq/tests/lifecycle_rust.rs`

## Build, replay and source identity scripts (4)

- `scripts/lifecycle_native_build.ps1`
- `scripts/lifecycle_native_cases.json`
- `scripts/lifecycle_native_identity.ps1`
- `scripts/lifecycle_native_replay.ps1`

## Public explanations and append-only decision records (4)

- `docs/DIGESTION_LOG.md`
- `docs/FAMILY_SUMMARY.md`
- `docs/internal/DESIGN_DECISIONS.md`
- `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`

## Local contract, replay sources and compact evidence (62)

- `docs/internal/extensions/lifecycle-native1/ACCEPTANCE_MATRIX.frozen.md`
- `docs/internal/extensions/lifecycle-native1/ACCEPTANCE_MATRIX.md`
- `docs/internal/extensions/lifecycle-native1/AXIOMS.json`
- `docs/internal/extensions/lifecycle-native1/BASE_IDENTITY.json`
- `docs/internal/extensions/lifecycle-native1/CHANGED_FILES.md`
- `docs/internal/extensions/lifecycle-native1/COMMANDS.md`
- `docs/internal/extensions/lifecycle-native1/COMPILED_ROUTE_EVIDENCE.md`
- `docs/internal/extensions/lifecycle-native1/CONTINUITY.md`
- `docs/internal/extensions/lifecycle-native1/CONTRACT_AMENDMENT_01.json`
- `docs/internal/extensions/lifecycle-native1/CONTRACT_REQUIREMENTS.json`
- `docs/internal/extensions/lifecycle-native1/EXPORT_DIAGNOSTICS.json`
- `docs/internal/extensions/lifecycle-native1/EXPORT_MUTATIONS.json`
- `docs/internal/extensions/lifecycle-native1/FINAL_STREAM_CONTROL_MAP.json`
- `docs/internal/extensions/lifecycle-native1/FINAL_STREAM_MAPPING_EVIDENCE.md`
- `docs/internal/extensions/lifecycle-native1/GUIDE.md`
- `docs/internal/extensions/lifecycle-native1/NATIVE_CLIENT_SELECTOR_EVIDENCE.md`
- `docs/internal/extensions/lifecycle-native1/NATIVE_COMMENT_AMENDMENT.json`
- `docs/internal/extensions/lifecycle-native1/NATIVE_CONTROL_EVIDENCE.md`
- `docs/internal/extensions/lifecycle-native1/NATIVE_EXECUTION_EVIDENCE.md`
- `docs/internal/extensions/lifecycle-native1/NATIVE_EXPECTATIONS.json`
- `docs/internal/extensions/lifecycle-native1/NATIVE_REFRESH_EVIDENCE.md`
- `docs/internal/extensions/lifecycle-native1/NATIVE_REFRESH_PLAN.md`
- `docs/internal/extensions/lifecycle-native1/NATIVE_SELECTOR_CONTROL_EVIDENCE.md`
- `docs/internal/extensions/lifecycle-native1/OWNED_DESCENDANT_CONTROL_EVIDENCE.md`
- `docs/internal/extensions/lifecycle-native1/PAUSE_CHECKPOINT.md`
- `docs/internal/extensions/lifecycle-native1/PREDECESSOR_DLL_REUSE.md`
- `docs/internal/extensions/lifecycle-native1/PROOF_EVIDENCE.md`
- `docs/internal/extensions/lifecycle-native1/REPORT.md`
- `docs/internal/extensions/lifecycle-native1/ROUTE_COVERAGE_EVIDENCE.md`
- `docs/internal/extensions/lifecycle-native1/RUNTIME_LAYOUT_SOURCES.json`
- `docs/internal/extensions/lifecycle-native1/RUNTIME_LAYOUT_SOURCES.md`
- `docs/internal/extensions/lifecycle-native1/RUST_DIAGNOSTICS.json`
- `docs/internal/extensions/lifecycle-native1/RUST_MISUSE_EVIDENCE.md`
- `docs/internal/extensions/lifecycle-native1/START.json`
- `docs/internal/extensions/lifecycle-native1/STARTUP_AMENDMENT.md`
- `docs/internal/extensions/lifecycle-native1/STARTUP_AMENDMENT.patch`
- `docs/internal/extensions/lifecycle-native1/STARTUP_AMENDMENT_RESULT.json`
- `docs/internal/extensions/lifecycle-native1/VALIDATION_APPLICABILITY.md`
- `docs/internal/extensions/lifecycle-native1/VERIFICATION_PLAN.md`
- `docs/internal/extensions/lifecycle-native1/axiom_inventory.ps1`
- `docs/internal/extensions/lifecycle-native1/default_build.ps1`
- `docs/internal/extensions/lifecycle-native1/export_mutation_replay.ps1`
- `docs/internal/extensions/lifecycle-native1/final_checks.ps1`
- `docs/internal/extensions/lifecycle-native1/final_stream_controls.ps1`
- `docs/internal/extensions/lifecycle-native1/final_stream_controls.scope_seed.json`
- `docs/internal/extensions/lifecycle-native1/final_stream_mapping_controls.ps1`
- `docs/internal/extensions/lifecycle-native1/final_streams.ps1`
- `docs/internal/extensions/lifecycle-native1/init_probe.c`
- `docs/internal/extensions/lifecycle-native1/loader_probe.c`
- `docs/internal/extensions/lifecycle-native1/native_client_selector_controls.ps1`
- `docs/internal/extensions/lifecycle-native1/native_clients.json`
- `docs/internal/extensions/lifecycle-native1/native_clients.ps1`
- `docs/internal/extensions/lifecycle-native1/native_control_selector_controls.ps1`
- `docs/internal/extensions/lifecycle-native1/native_controls.json`
- `docs/internal/extensions/lifecycle-native1/native_controls.ps1`
- `docs/internal/extensions/lifecycle-native1/native_recipe_controls.ps1`
- `docs/internal/extensions/lifecycle-native1/native_selector_controls.json`
- `docs/internal/extensions/lifecycle-native1/native_selector_controls.ps1`
- `docs/internal/extensions/lifecycle-native1/owned_descendant_control.ps1`
- `docs/internal/extensions/lifecycle-native1/rust_misuse_replay.ps1`
- `docs/internal/extensions/lifecycle-native1/rust_misuse_selector_controls.ps1`
- `docs/internal/extensions/lifecycle-native1/scope_check.ps1`
