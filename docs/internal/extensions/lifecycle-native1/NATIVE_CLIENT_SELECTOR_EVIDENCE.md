# Native client selector evidence

The client selector leaf passed all thirteen actual PowerShell callers in
`.lake/lifecycle-native1/client-selector-controls/20260923T093748354-584c85f0/RESULT.json`.
The receipt SHA-256 is
`60ED495D2249A487C889FE314EE24EAC040DD8CB544D85AFC70F6EDB5C036107`.
An independent retained-byte review on 2026-09-27 UTC is recorded beside it as
`REVIEW-20260926.json` (the filename uses the local review date). It rechecked
all 36 retained source/tool/caller/registry pins and all 104 raw capture pins,
the complete ordered control roster, every actual ordinary exit and exact
stdout/stderr bytes, and the absence of the disposable tree. All passed.

The script and its dependencies remain byte-identical to the successful run.
The unchanged complete control set was therefore reused rather than rerun.
No native client or compiler was invoked, and no heavy-build mutex was acquired.
The caller processes took 1.6303988–3.346126 seconds under their positive
30-second owned-process deadlines. Every launcher reports a Windows
`kill-on-close-job`, no timeout, no overflow, and no retention error.

## Reproduction and scope

Run `native_client_selector_controls.ps1` in this directory with the pinned
PowerShell host. The harness invokes the real `native_clients.ps1 -Phase Validate`
parameter boundary in fresh callers. It gives every caller a nonexistent build
receipt. Success or the exact selector rejection must occur without reading
that receipt or creating the copied repository's `.lake` directory.

Each disposable runner differs from production in exactly one root-path
expression; retained bytes confirm this substitution is the only edit.
All five copied helpers are byte-identical. The registry cases use the same
production classifier; they do not substitute a copied validation predicate.
The original `finally` checked 67 pins, performed zero restoration writes to
live sources, and removed the disposable tree after checking its path and
rejecting reparse points. Integrity and cleanup have separate `finally` paths.

The following source identities define applicability:

| Source | SHA-256 |
| --- | --- |
| `native_client_selector_controls.ps1` | `FA96E34698745E189EBFFE34EE1BEFD471A1AE32EC97C2CA7BFBBB5AACD5B92A` |
| `native_clients.ps1` | `FA8EC7976BBD744636BB530C609BB229044F58FC6CEAA5F3FA825B3E039125EC` |
| `native_clients.json` | `5A8B5E6A30482209EA7F75D1733DCAAC5199B5468BAB3D36000F364284AFE3B2` |
| `scripts/lifecycle_native_identity.ps1` | `0E13FCB128193D895D5CAAA94D3BF3ECED511910360E524D8D5C17B3A3F7365A` |
| PowerShell executable | `362A356CE7F0940EC74F73A8FC2C990A2CC24A38A11C90BBD8ECA947110AD139` |

The receipt also pins the unchanged owned-process, strict-stream, integrity,
and raw-byte child-source helpers. Changing a consumed source or tool invalidates
reuse of this receipt. Unrelated Lean edits do not affect this validation-only
caller evidence. Governance preflight passed again at
`7b227c49ef2ec044b702126cc41c9add847eed01`, with `rmq-proof-sprint` required and
all three actual canonical RMQ runtime skills present. HEAD was
`3dbdebedcc6ba6b2a864df0d46dcc09ccaaa7536` on
`codex/life-native-1-consuming-owner`.

## Exact controls

The two accepted callers have ordinary exit zero and empty stderr. Their stdout
is exactly `NATIVE-CLIENTS VALIDATED cases=<count> ids=<ordered comma-separated IDs>`
followed by CRLF. Omission selects all ten IDs in `native_clients.json` in order;
the focused caller selects only `LN1-RUST-OWNER-ERRORS`.

Each rejected caller has ordinary exit one, empty stdout, and stderr exactly
`CLIENT-SELECTOR REJECT: NATIVE-CLIENTS: <message>` followed by one LF. The
messages below are complete suffixes, with no other output accepted.

| Ordered control | Expected result or complete rejection message |
| --- | --- |
| `caller-omitted` | Accept; ten ordered IDs; 263 stdout bytes |
| `caller-known` | Accept; only `LN1-RUST-OWNER-ERRORS`; 60 stdout bytes |
| `caller-null` | `explicitly empty selector` |
| `caller-empty-array` | `explicitly empty selector` |
| `caller-empty-string` | `empty or whitespace selector` |
| `caller-whitespace` | `empty or whitespace selector` |
| `caller-unknown` | `unknown selector LN1-UNKNOWN` |
| `caller-duplicate` | `duplicate selector LN1-RUST-WORD` |
| `registry-missing-middle` | `registry schema/count differs` |
| `registry-duplicate-middle` | `frozen mapping differs at LN1-RUST-POST-TAKE-FAILURE` |
| `registry-reorder-middle` | `frozen mapping differs at LN1-RUST-OWNER-ERRORS` |
| `registry-handler-mismatch` | `frozen mapping differs at LN1-RUST-OWNER-ERRORS` |
| `registry-verdict-mismatch` | `frozen mapping differs at LN1-RUST-OWNER-ERRORS` |

Missing, duplicate, and reordered middle cases alter both the ID list and the
case list. Handler and verdict mutations preserve both rosters and counts.
They therefore challenge the independent ordered ID-to-handler/verdict mapping,
not merely a total number of passes. The missing case reaches the schema/count
check; the other four registry mutations reach the exact production mapping
check. The two expected-accept callers prevent universal rejection from passing.

## Requirement coverage and remaining integration

The verbatim requirements remain frozen in `CONTRACT_REQUIREMENTS.json` and
`ACCEPTANCE_MATRIX.frozen.md`; this leaf does not alter those rows or declare the
whole LIFE-NATIVE-1 candidate complete.

| Frozen row | Evidence supplied by this leaf | Separate integration requirement |
| --- | --- | --- |
| N1-21 | Actual omitted, focused, null, empty-array, empty-string, whitespace, unknown, and duplicate caller binding; full ordered mapping rejects missing/duplicated/reordered middle entries and wrong handler/verdict; no runtime output mutation. | Run the focused native client and then all ten native cases using the current successful build receipt; confirm actual per-ID dispatch/results. |
| N1-20 | Exact ordinary exits and retained physical stdout/stderr, strict UTF-8 and ordinal production predicate, all raw pins reviewed, independent integrity and disposable cleanup. | Hostile stream, output-overflow, and forced partial-setup controls are separate evidence; these thirteen callers alone do not establish those categories. |
| N1-22 | Every caller used the existing owned-process facility with a positive 30-second deadline, preserving captured failures; no expensive stage or mutex acquisition. | The separate descendant termination control establishes timeout cleanup. Native execution still requires the shared heavy mutex, evidence-based execution deadlines and pinned artifact/dependency closure. |
| INV-MUTATION-REPRODUCIBILITY | Versioned runner contains all thirteen mutations/accept controls and exact expected diagnostics; actual copies and captures are retained, helpers unchanged, scratch removed. | Include the runner, registry, and this evidence with the eventual candidate commit. No commit was authorized for this leaf. |

The production strict-stream predicate reads the physical byte files; it does
not accept the inherited helper's returned-line arrays, whose newline information
can be lost. The only line output used here is independently checked against
the exact captured CRLF or LF bytes.

The ten unexecuted semantic cases are the two C++ models, two Rust models,
Rust owner errors, post-take failure, three runtime-conflict orders, and
initialization failure. They require freshly applicable lifecycle DLL/client
artifacts after the Lean runner refinement, adjacent pinned runtime staging,
and the historical DLL fixtures solely for the explicit runtime-conflict cases.
Historical fixture reuse must retain its disclosed provenance limit. No native
semantic result, allocation result, or constructor runtime is inferred from
these validation-only controls.

The proof-digestion point is narrow: callers cannot silently replace an explicit
empty selection with the full registry, and mutating a middle case's handler or
verdict cannot preserve acceptance merely by keeping its ID and pass count.
The live assumption is the reviewed source/tool identity and certified Windows
host. A skeptical reviewer should next inspect actual dispatch and native
results for the same ten cases; that work belongs to the native execution leaf.
No new design or process decision was made, so no ledger append was needed.
Full Lean builds and broad gates were skipped because this leaf changed only
the evidence document and reviewed already completed validation-only captures.
