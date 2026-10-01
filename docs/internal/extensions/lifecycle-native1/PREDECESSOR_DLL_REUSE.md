# Predecessor DLL discovery, 2026-09-23

This read-only check locates historical fixtures for the Rust runtime-conflict
regressions. It does not replace the newly built lifecycle DLL, run either old
DLL, or certify a fresh predecessor build. No files outside this workspace were
copied or edited.

The matching worktree is `C:/Users/poin/.codex/worktrees/1817/RMQ`, HEAD
`4edb1e14f607a809c018d569c3d4be99c0c54959`. Targeted checks of the corresponding
`build` and `binary-build` directories in native-p0 worktrees 367c, 587c, af4b,
eafd and the reviewed native-adapter-base found no competing artifacts.

| Artifact relative to that worktree | Actual SHA-256, matching adjacent manifest |
| --- | --- |
| `.lake/native1/build/packed_route.dll` | `CB53991D47129B608F364A7B0525E983321215E3DACE71661C7ECE950C8E991B` |
| `.lake/native1/binary-build/packed_rmq.dll` | `7605525E9E89540D43DFD307E84DE24F03062A9632A59062682600D20E0168C4` |

Both directories contain `build-manifest.json`. Their hashes are respectively
`B07F660A24BA5966D7CD5BDA3D2C7C7D90ECF6FDD4192DE0B709C486D5F006F9` and
`A4C20BCAA5E35402293DB522CE8736A81BD84FBC67FC2648693475504E5E1069`.

All nine route Lean sources and all nineteen binary Lean sources, plus their
old C shims, headers and export definitions, match the manifests in the current
checkout. Of the complete source-pin lists, route has 15/19 matches: the changed
files are `src/lib.rs`, `Cargo.toml`, `scripts/packed_native_build.ps1` and
`scripts/packed_native_identity.ps1`. Binary has 29/31 matches: only `src/lib.rs`
and `Cargo.toml` differ. These Rust clients are not being reused.

For both manifests, the installed seven selected compiler/runtime pins match:
`lean.exe`, `leanc.exe`, `lean.h`, `libleanrt.a`, `libInit_shared.dll`,
`libleanshared.dll`, and `libleanshared_1.dll`. This check did not rehash either
manifest's entire 4,856-file Lean inventory or its Rust/C++ tool inventories.
The existing `Get-LNDependencyClosure` PE reader found one non-system dependency
for each DLL: `libInit_shared.dll`, whose actual hash matches both manifests.
Each closure also has fourteen system/API-set imports, under the helper's
documented external OS-resolution boundary; neither has delay imports.

Binary's `native1-binary-build-v1` manifest uses `native1-toolchain-v3` and its
nineteen generated-C hashes still match the files in that old worktree. Route's
`native1-build-v2` manifest uses the older `native1-toolchain-v1` and has no
generated-C ledger. Its nine current generated files match their current cache
records, but those records were superseded by binary's later toolchain-v3 digest;
they cannot retrospectively supply route's missing generated-C ledger.

The DLL identities and unchanged C/Lean interfaces support narrowly labeled
historical runtime-conflict fixtures. They do not establish whole-manifest
current-checkout reuse, nor make route equivalent to a freshly certified
toolchain-v3 build. Before actual regression execution, the coordinator must pin
these exact DLLs/manifests and the freshly resolved runtime dependency alongside
the new Rust test executable. Production lifecycle execution continues to use
the new `packed_rmq_lifecycle.dll` exclusively.
