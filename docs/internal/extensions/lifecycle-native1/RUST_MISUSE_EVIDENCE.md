# Rust ownership controls

The real facade is compiled before independent misuse callers. The committed
runner is `rust_misuse_replay.ps1`; these metadata-only clients neither construct
foreign handles nor perform undefined-behavior experiments. Its ordered mapping
contains fifteen expected rejections and two expected accepts. The complete
historical diagnostic discovery and reviewed exact replay both passed. Current
Discovery and Replay reproduce every diagnostic byte, as distinguished below.

The current mapping SHA256 is
`8c5f71775d51a892b23267b79ddf60982b77bdb1174ca83ee7efe0e977ec7de6`.
It covers Send and Sync for Runtime, Owner, Observation, Natural and QueryResult;
owner cloning; mutation through an immutable borrow; bytes escaping their result;
private raw-handle access; and an owner escaping its initializing runtime. The
positive clients use a mutable owner borrow and a correctly scoped result view.

The runtime-escape caller explicitly drops its answer before returning the owner.
The earlier tail-tuple form produced an incidental temporary-lifetime diagnostic;
that failed discovery is retained at
`.lake/lifecycle-native1/rust-misuse/20260923T091720037/RESULT.json`.
The owner-clone caller's actual diagnostic is E0277, not the earlier guessed
E0599; the earlier failure remains at
`.lake/lifecycle-native1/rust-misuse/20260923T091549350/RESULT.json`.
Neither failed attempt certifies the complete registry.

## Actual selector and mapping controls

`rust_misuse_selector_controls.ps1` passed all fifteen controls at
`.lake/lifecycle-native1/rust-selector-controls/20260927T063015001/RESULT.json`.
It took 87.48 seconds overall. Each actual PowerShell caller had its own
30-second owned deadline. All eight live source/helper/tool pins remained equal;
the disposable shadow was removed. No compiler or native child was invoked.

The controls check omitted and focused selection; explicitly bound null, empty
array, empty string, whitespace, unknown and duplicate selectors; and deletion,
duplication and permutation of middle mapping entries. Four new holdouts append
NUL, soft hyphen, zero-width space or BOM to a known ID and reject before compiler
dispatch. OnlyCase now uses ordinal membership, closing the cultural comparison
gap. All preceding eleven controls are retained. Full stdout and stderr
are compared ordinally with the actual ordinary exit. An absent toolchain
sentinel makes accidental compiler dispatch fail. These controls establish the
caller/mapping boundary, not the Rust type-system rejection results.

This receipt supersedes the eleven-case selector result at
`rust-selector-controls/20260927T043337825` because the production guard changed.
The 17 semantic caller bodies, expected error codes and their ordered mapping
remain unchanged. The semantic receipts below are historical until refreshed
against this runner and the qualified Rust documentation comment. The final
section records that completed refresh.

## Reviewed diagnostic discovery

All17 actual cases passed at
`.lake/lifecycle-native1/rust-misuse/20260927T050848252/RESULT.json`.
Root read every full diagnostic before freezing RUST_DIAGNOSTICS.json
(SHA256 `73986b4874784bb6a97b722e430f30634b30050b17a12ce9ed6c92ccb2897767`).
The full ordered mapping has10 thread-trait rejects and5 independent ownership,
borrow or privacy rejects, plus2 expected accepts. Multiple E0277 messages for
one caller concern the same intended Send/Sync obligation, including raw pointer
and Runtime marker dependencies. The exact replay preserves every diagnostic
byte, source hash, ordinary exit and source/tool/runner fingerprint; it is
separate from this reviewed discovery.

## Historical exact replay

All17 fixed cases replayed successfully at
`.lake/lifecycle-native1/rust-misuse/20260927T051519397/RESULT.json` (receipt SHA256
`e78fef373384b29a3deb201be28fb83185151fe84b25eaf4c8801550eeee0329`).
The complete ordered15reject/2accept roster, full expected streams and ordinary
exits match the reviewed frozen manifest. All112 source/tool/fixture
pins remained unchanged and the mutex was released. These are actual compiler
executions against the real safe facade, separate from its actual native runtime
clients and separate from universal claims about arbitrary unsafe C callers.

## Current discovery, provenance rebind and exact replay

Current Discovery passes at `rust-misuse/20260927T072740867/RESULT.json`, SHA256
`b7fae4e0276428c4bf33dbce9c2ff2ae35dc965bb70424defb559f8bf24393eb`.
Every one of the 17 complete case objects equals its historical reviewed object:
ID, expected code, source hash, full stdout/stderr and ordinary exit. Their
canonical exact JSON SHA256 is
`9d686c79df9b519227035fd9051dcd79e3b4d9a3b55ba8bf216cef4d9290ed26`.
Root independently rehashed all 111 source/tool/fixture pins and 144 raw pins
from 18 actual compiler captures. The facade compiles with empty streams before
the fifteen intended rejections and two acceptance controls.

The complete current fingerprint is
`12c2881f6c9b5a08698a2a8d29054adf11a3c1e5175a2b0a5f1ef862eefd6a58`.
All 93 producing source/tool rows contribute. The runtime's property sort on
ordered dictionaries permutes equal missing keys; it does not discard any row.
Root checked that complete permutation against the original exact row multiset
and reconstructed the fingerprint. Neither insertion order nor canonical path
sorting is claimed. A changed enumeration can conservatively reject a replay.

Only the manifest's fingerprint and appended provenance note change; all 17
diagnostic cases remain intact. Current `RUST_DIAGNOSTICS.json` is 35435 bytes,
SHA256 `985835ed2ac39483dae006c327f656a0fd92546d60c91ef97122f67b6d795141`.
The archived previous bytes and actual recipe order are pinned in its review.

Complete Replay passes at `rust-misuse/20260927T073749082/RESULT.json`, SHA256
`921ceca64185a1ed5950ec219ed5ff3c0c3451bdd14c6507205f71af38844f5d`.
The complete ordered fifteen-reject/two-accept roster reproduces every frozen
diagnostic byte and ordinary exit. All 112 integrity pins pass; the mutex is
released. All 18 actual and launcher exits match, with no timeout, output
overflow or retention error. The maximum actual compiler time is 0.459644 s;
their sum is 3.7422575 s. These compiler checks remain separate from native
runtime executions and foreign-caller preconditions.
