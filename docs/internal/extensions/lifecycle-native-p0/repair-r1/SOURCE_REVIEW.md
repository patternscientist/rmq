Status: BOUNDED_READ_ONLY_REVIEW_COMPLETE

Independent helper: /root/review_dependency, inherited parent model/runtime,
read-only source/inventory review at worktree 587c/RMQ and exact base
0c873072e84be9e1d65edab1985bcff1d23abef1. Governance preflight passed at
7b227c49ef2ec044b702126cc41c9add847eed01 with required rmq-proof-sprint and
actual catalog rmq-audit-prompt, rmq-coordinator, rmq-proof-sprint. No external
auditor bridge was used. This is source review, not campaign acceptance.

The helper reviewed the complete historical source/receipts and the new runner,
helper and controls. Independent byte inspection derived eleven local PE nodes:
lean.exe, leanc.exe, clang.exe, ld.lld.exe, libInit_shared.dll,
libleanshared.dll, libleanshared_1.dll, libclang-cpp.dll, libLLVM-19.dll,
libc++.dll and zlib1.dll. The original receipt omitted the last four compiler
dependencies. zlib1.dll is imported by ld.lld.exe and libLLVM-19.dll. Every
inspected delay directory is zero. Read-only execution of the production
dependency functions reproduced eleven nodes and complete membership.

| Missing historical file | Bytes | SHA-256 |
| --- | ---: | --- |
| libclang-cpp.dll | 82430464 | D4028A751017B44681373A4BEC8381B120A06083AC688DCDF45F45AEC46783C6 |
| libLLVM-19.dll | 80710656 | 74A1A54619E989CDC1F52EA3F206DA83C3C55DB73594FD1D4D4F2FE6D49CC02D |
| libc++.dll | 1636864 | 1F3D0FF8504F19E6B6DC98426B58FA60B6A571D027F2C6AC4E169637C63A95DE |
| zlib1.dll | 110592 | 260997C016819F60CEF902F3E7C0267804785D7B70C87CF541D0E40E6B693C75 |

Installed Leanc.lean and binary strings ground the invoked compiler/linker roots:
leanc uses the compiled ROOT/bin/clang.exe absent the rejected overrides, and
the compiled internal flags include -fuse-ld=lld. This is source reasoning,
not a verified compiler or dynamic loader trace. OS/API-set resolution, dynamic
LoadLibrary behavior and PowerShell/.NET remain external assumptions.

The historical bea5ce75f788c4035031ba81e69d8de36eda3f92 runner has 41479 bytes,
SHA-256 077BF8D478141F8891AB6F9C2E332CBF8C8F75ACA32C722B29BD307924957B8E.
Original RESULTS has 63804 bytes,
6440A963BE7A0E65222F86AFE3CFB89E4BEE1B6BDCD0226DC0D5CDA88D296FDD.
Its raw summary has 131413 bytes,
0E7DCC42E1EA66C0FF1C8A8AD7ED791FEA786189FA6E38A52BF8B5B55954CD12.
Strict Git byte reads supply these identities; no shell newline serialization
was used. verify_contract.py rechecks the named blobs and retained pins.

Source-review feedback and implemented responses:

- Pin raw stage files before strict decoding, since malformed UTF-8/JSON can
  otherwise bypass capture. The runner now does so; a raw FF control exercises it.
- Preserve the original stage error if available compile-output capture fails.
  Get-LNAvailablePin records independent capture errors, and the production
  finalizer consumes them. A real exclusive file lock plus exit-seven stage
  exercises the joint failure.
- Compare exact native/launcher exits, streams and complete integrity errors.
  Controls now check these, including empty timeout/launcher streams; dependency
  file mutations require exactly changed-pin plus tree-change errors and a
  manifest-hash mutation exactly the changed-pin error.
- Restore ignored link maps even if summary parsing fails. Restoration now
  enumerates confined owned fixture paths independently of summary availability.
- The isolated fixture splice preserves the whole production setup/functions
  prefix and catch/finally/verdict suffix. It replaces only the stage body and
  executes actual owned subprocesses. It is not an extracted-finally replay.

The helper found no additional runner architecture defect in its final bounded
check. The last two exact-assertion refinements above were applied by the lead
after that response. Final execution receipts, rather than this review narrative,
determine their outcomes.

Independent claim/baseline reuse inspection verified 2910 outside-rescan paths
and bytes, 1125 Lean/Lake/toolchain paths with working hashes and HEAD blobs,
and 251 distinct historical evidence pins. Ripgrep outside enumeration contained
2870 identical paths in each worktree; production attribution enumeration 2881;
11640 production path-normalization comparisons agreed. Relevant root ignore
behavior and Git common directory agree. No claim scan or build was run by the
helper. Scanner/policy/rg/config/PowerShell identities match:

| Context | SHA-256 |
| --- | --- |
| Original outside-file snapshot | 93DE2690CB6509033FC93F3BDD7BA42CEF2E21F9A0AA9761DC04DF511EB0F8F4 |
| Claim scanner | 5310DBA1242B3ED4A0B054A15B1B6911C056C228B2711F3D958EAB539BB3F6F7 |
| Claim policy | 4096C7A708DF686F0AC7B62D935B22C13C1F1212494A3B39FD2ADD127AD43CD9 |
| Ripgrep | BAEE1BC8559B7494F2F2FA61C0AFD48DC32A3A9420D40832B1C53FDE59A31B01 |
| PowerShell 7.6.5 executable | 362A356CE7F0940EC74F73A8FC2C990A2CC24A38A11C90BBD8ECA947110AD139 |

RIPGREP_CONFIG_PATH is absent. The exact rg executable remains under
C:/Users/poin/AppData/Local/OpenAI/Codex/bin/6dd87ad08d6ff997/rg.exe.
The final coverage composition still requires the final unchanged-policy rescan
of lifecycle-native-p0 and both ledgers. It is not a new default-root scan.

Digestion: stronger failure evidence and concrete compiler identity do not
strengthen the unchanged finite ownership measurements into a universal heap
bound. The skeptical remaining local question is answered by final production
controls/replay; the consuming adapter and campaign aggregate/audit are separate
downstream work.
