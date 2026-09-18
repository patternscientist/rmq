# OPT-1 continuation verification ledger

Status: INCOMPLETE; local composition/replay finished, external final phase requested.
Checkpoint: 8e355fda7788077f548865c1d6acf2ae5e88da55.
Governance/base: 0e6a00f654abc64f8b68988fa9675b9a839dca2f.

The existing session completed 250 prerequisites, then returned an ordinary
Capstone error. A materially repaired one-module run passed in 14.083s; the
exact checked source and receipt are retained separately from the current
full-capstone draft. All 35 frozen requirement rows remain byte-identical.

The sole Lean slot rotates explicitly among disjoint source owners. Root
first checked the concrete budget; generic emitter/semantic/safety ownership
passed to bound_proof; static accounting/Query ownership follows with
source_relations; root next checks QueryProof/QuerySafety/Certificate/Capstone/
Consumers; runtime_replay then checks executable startup and the exact registry.
No owner launches a process without explicit transfer after the prior process
has exited. While waiting, owners prepare proofs, independent source reviews
and replay infrastructure. A routine owned build is not an external blocker.

## Commands and distinct coverage

| Role | Planned command / scope | Acceptance purpose | Runtime/deadline |
| --- | --- | --- | --- |
| Development, completed | existing build session 34305; then one-module capstone-resume-plan | concrete original-run bound and full Run small-fuel equality, REQ-OPT-BUDGET | original failed module 8.808s; repaired 14.083s, deadline120s |
| Development | compact-proof-development/check.ps1 one module at a time | actual emitter, universal RunsTo/adequacy, early stop and prefix safety | first Compact12.803s, proof13.141s then12.800s, safety26.348s; worker records each deadline/attempt |
| Development | compact-static-development/check.ps1 and fixed numeric consumers | constructor-exhaustive field fit, protected/unused registers, literal code encoding and accounting | static15.279s and Types6.565s; worker records numeric measurement separately |
| Development | scripts/packed_optimized_build.ps1 -PlanPath docs/internal/extensions/opt1/root-composition-plan.json -EvidenceDirectory docs/internal/extensions/opt1/composition-development -ModuleDeadlineSeconds 180 -TotalDeadlineSeconds 1200 | direct new query joins and every exact field consumer, REQ-OPT-RUN/SPACE/CONSUMER and inherited same-object/safety rows | warm query module observed14.083s;180s per-module margin,1200s plan; no full fallback |
| Development then final registry | scripts/packed_optimized_runtime.ps1 -StartupOnly; one known selector; production registry after source freeze | actual semantic reach, independent oracle/control cases, strict selectors and owned deadlines | runner captures startup/focused/full limits; diagnose slow initialization before changing timeout |
| Final dependency campaign | scripts/packed_optimized_certificate_replay.ps1 | fixed expected-type consumer rejects every field deletion/weakening after altered producer compiles; expected-accept controls and restoration | prepare registry before launch; isolated case artifacts and owned processes; exact source snapshots |
| Final-required | new capstone/consumer axiom inventory and explicit imports; original-base and continuation-base whitespace ranges; strict design/claim scans | exact trust/public surface and policy checks | only after consuming source stabilizes; unrelated checked generic artifacts are scheduling evidence until final import |
| Externally scheduled final phase | lake build / aggregate only in coordinator-granted host-wide slot; fresh blind exact-commit audit | complete candidate certification and independent acceptance evidence | not launched while compact/query obligations are unverified |

Every build receipt names the exact source SHA and process outcome. The root
build helper now retains timestamped attempts as well as its latest receipt,
so a repaired run cannot overwrite the failure evidence. No receipt-only
observation is treated as proof of compact semantic equivalence.

## Completed local plan and remaining external phase

The generic, static and whole-query proof stages all completed with exact
source evidence; ac5af8e416f906391dc117f083a883acc053a268 freezes the checked
proof and full 27-case semantic registry. The 93-root axiom union and all
78 typed consumers passed. After preserving and repairing the actual A01
import-root failure and two diagnostic witnesses, bbbe652fa41fa40bf2530b5e2f09c4c225c0e896
freezes the successful full 80-case certificate campaign. All 160 producers
compiled before their fixed consumers, with exact expected verdicts and
restoration. Independent raw-receipt reconstruction confirms the outcome.

Final consolidation changes reports and receipt-verification artifacts only;
all 19 load-bearing checked source hashes remain equal. Report-sensitive
claim/design/hygiene and exact-range checks accompany the final checkpoint.
The only unexecuted plan row is the explicitly coordinator-scheduled final
aggregate/acceptance phase requested in SCHEDULED_FINAL_REQUEST.md. No ordinary
proof or replay process is left running as a resource-wait endpoint.
