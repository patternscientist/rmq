# Default RMQ cache preparation

This is an isolated cache-preparation leaf. It does not certify `lake build`,
Native execution, or candidate-wide acceptance. Governance preflight passed at
`0e6a00f654abc64f8b68988fa9675b9a839dca2f` with the actual three-skill runtime
catalog and required `rmq-proof-sprint` skill.

Frozen before helper edits:

| ID | Exact assigned requirement | Required evidence |
|---|---|---|
| CACHE-MODE | "preserve existing default249 behavior" | Optional mode leaves the prior canonical hydration path intact. |
| CACHE-CLOSURE | "Derive372 closure from actual imports" | Source-derived topological closure has exactly 372 local modules. |
| CACHE-IDENTITY | "require identical source/toolchain/Lean commit traces; hash source+each copied artifact before/after" | Both checkouts' source/toolchain pins and each copied artifact remain identical across copying; source trace names pinned Lean commit. |
| CACHE-MISSING | "copy ONLY491 missing artifacts, never overwrite any existing path" | A frozen 491-entry plan; exclusive no-overwrite copies; destination hashes equal before/after source hashes. |
| CACHE-BOUNDARY | "only this worktree writes,2fb8 read-only" | Distinct registered source checkout; all destinations resolve below this worktree's `.lake/build`; no links or foreign writes. |
| CACHE-NATIVE | "Record zero imported Native modules/default-root difference" | The RMQ closure contains zero Native modules; the separate Native import checks remain required. |
| CACHE-DEFER | "DO NOT invoke Lean/Lake or any fallback build yet" | Copy-only receipt and a pending explicit Lake validation command; no compiler or build invocation. |

The production loop is the focused positive control. Exact count, source,
compiler-trace and missing-path checks fail closed before copying; the final
copy operation itself refuses to replace an existing file. The root coordinator
owns subsequent Lake validation and any narrow rebuild it demonstrates is
needed. No broad policy replay or Lean check is appropriate for this leaf.

The optional `-DefaultRMQ` mode derives the actual import header, skipping line
comments and nested block comments and stopping at the first declaration. The
372-module closure has only `Std` as an external import and no Native modules.
The original 249-module mode remains the default; its source tail is unchanged
after line-ending normalization, SHA256
`9E02BEFC8E445E2DD71103854EC349DB77D41FD73A90242BCC70BB30EC8AF393`.

The new mode requires the registered `2fb8` checkout, exact source and toolchain
bytes, and the pinned compiler marker in every foreign module trace. It freezes
the 491 missing paths before copying, checks that destinations stay within this
worktree's build directory without traversing links, and uses exclusive
no-overwrite file copies. SHA256 uses a bounded 1 MiB FileStream buffer; the
production hash function agreed with `Get-FileHash` for three samples including
a 1.6 MB object file. Every copied file receives before/after foreign hashes and
a destination hash; both source trees and toolchain files are rehashed afterward.

Focused evidence retained:

- `commands/hydrate-default-preflight.json`: syntax, three buffered-hash
  equivalences, and production rejection of this worktree as the foreign source.
- `commands/hydrate-default-parser-02.json`: three import-header controls,
  including nested comments and the actual documentation sentence that had
  confused the first whole-file regex. An initially incorrect expected import
  list in that test was corrected after inspecting the six-line source header.
- `commands/hydrate-default-command-01.json`: fail-closed import-parser diagnosis,
  12.424 seconds, zero files copied.
- `commands/hydrate-default-command-02.json`: all 372 source/trace/path checks
  completed, 491 missing files and 997 existing artifacts identified; a
  PowerShell 5 `Measure-Object` compatibility failure in progress formatting
  stopped the operation after 153.875 seconds, before any copy. Explicit
  arithmetic replaced that formatting operation and was checked in the actual
  Windows PowerShell runtime.

The hygiene scan found no matching forbidden Lean constructs, and the focused
whitespace check passed. No Lean source, public theorem, or runtime source was
changed. No Lean/Lake/native compiler was invoked by this leaf.

WDD rationale for coordinator integration: an optional source-derived default
closure mode reuses available identical-source artifacts while preserving the
already used canonical mode. Copying is isolated and never overwrites existing
files. The alternative of rebuilding hundreds of unchanged dependencies would
consume the shared compiler slot before checking whether their existing cache
is reusable. Artifact copying is only preparation: Lake must validate the copied
dependency and output hashes, and any demonstrated stale entries still require
a build. This does not waive compilation or change the proof trust boundary.

The final production copy passed in **189.603 seconds** under its 1800-second
owned deadline. It copied exactly **491 distinct files / 133,498,087 bytes**,
preserved **997 existing artifacts**, created no links and overwrote no existing
files. All 372 pairs of source hashes and both toolchain hashes remained stable;
all 491 before/after foreign artifact hashes equaled their destination hashes.
An independent receipt inspection confirmed the exact counts, unique paths and
zero hash mismatches.

- Copy manifest: `commands/hydrate-default-20260912T125020579.json`, SHA256
  `7C9CE0DB64D31F075FCBE16CF150049048E86BACD43B38AFD73C6432164D9A78`.
- Owned command receipt: `commands/hydrate-default-command-03.json`.
- Final helper SHA256:
  `9E98F0DB4395BDEBE953720140E1BBCC81352EA8A57A649F227CF74D3CD93D83`.
- Registered source checkout: `C:/Users/poin/.codex/worktrees/2fb8/RMQ`, HEAD
  `26d6b5c2b10ed06ae4f72d9075d746ede987bdab`.

All seven frozen `CACHE-*` rows are satisfied for this preparation leaf.
**CANDIDATE_COMPLETE applies only to the owned copy-preparation target.** The
root coordinator owns the next exclusive command, `lake --no-build build RMQ`,
followed by the required default build/gate as scheduled. The separate Native
import checks remain necessary.

Digestion: the missing default-library files are now local, byte-identical
copies of artifacts from matching source files. This saves avoidable compilation
if Lake validates the cache. It does not prove that a matching source file was
compiled against the current imported objects: a skeptical reviewer should next
inspect Lake's dependency/output validation. That check is deliberately pending,
and any failed entry must be rebuilt through the root's scheduled compiler slot.
