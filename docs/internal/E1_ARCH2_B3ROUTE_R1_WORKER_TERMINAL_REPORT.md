# E1-ARCH2-B3ROUTE-R1 — worker terminal report (as received)

**Classification: RECEIVED WORKER PROSE. UNTRUSTED UNTIL RECONSTRUCTED.**

Per `docs/internal/AUDIT_PROTOCOL.md`, worker prose, matrix statuses, terminal
transcripts, timings, and claimed verdicts are untrusted until reconstructed
from the exact committed tree. This file exists because the report was
delivered only in a chat session and would otherwise be unrecoverable; it is
archived as the *subject* of an audit, not as evidence.

Recorded 2026-07-23 by C05. Reproduced verbatim below the rule.

Coordinator verification of the structural claims (chain, cleanliness, path
scope, and the obstruction's derivation) is in
`E1_ARCH_ADDENDUM_C05_2026_07_23.md` §2. That verification is partial and its
limits are stated in §9 of the same file.

---

Status: OBSTRUCTED
Handle/title: `E1-ARCH2-B3ROUTE-R1` — `(E1-ARCH2-B3ROUTE-R1) Construct and decide the full historical bounded route`

The accepted pinned source reaches a subtraction that requires truncated `Nat` semantics but violates the frozen ordered/no-wrap requirement:

```
tick=71, pc=73, instruction=.sub 19 22 23
register 22=5, register 23=19
5 - 19 = 0
¬ 19 ≤ 5
```

The checked implication is:

```
source_simulation_and_ordered_subtraction_incompatible
    (state : State)
    (hpc : state.pc = 73)
    (hleft : state.regs 22 = 5)
    (hright : state.regs 23 = 19)
    (hordered : state.regs 23 ≤ state.regs 22) :
    False
```

This triggers the frozen architecture-choice stop condition. It is not a universal `HistoricalFAIL`, and no `HistoricalPASS` is claimed.

## Exact candidate identity

* Worktree: `C:\Users\poin\.codex\worktrees\bb61\RMQ`
* Branch: `codex/e1-arch2-b3-historical-route-r1`
* Base: `c19061629ce8cf1e78992a99346170edd84b4971`
* Base tree: `bf10934b4034aaf3dade21a448dd246cf51e5c69`
* Freeze: `0554c0f7ad031f43c99aa3b4457fc5168268abb4`
* Freeze tree: `903c00b4458751d6dc4ec3c7ca39ea6c962f6e1e`
* HEAD: `bc71cad140956477f4de7e513529ae15d381aa13`
* HEAD tree: `0ed3235d926c190adacdc8babc28c7acfa06490f`
* Parent chain: base → freeze → HEAD
* Worktree/index/untracked state: clean

Exactly two commits follow the base. Commit 1 is matrix-only; commit 2 changes exactly the five authorized paths.

## Durable evidence

* `RMQ/Validation/E1Architecture/B3HistoricalRoute/Obstruction.lean:67`
* `docs/internal/E1_ARCH2_B3_HISTORICAL_ROUTE_MATRIX.md:517`
* `scripts/e1_arch2_b3_historical_route_replay.ps1:174`
* `docs/internal/DESIGN_DECISIONS.md:5072`
* `docs/internal/WORKFLOW_DESIGN_DECISIONS.md:6411`

Checked objects include:

* `SubUnderflowObservation`
* `firstSubUnderflow`
* `pinnedFirstSubUnderflow`
* `denseSegB_underflow_slot_numeric`
* `denseSegB_underflow_pc`
* `pinned_source_subtraction_is_truncated`
* `pinned_source_subtraction_is_not_ordered`
* `ordered_subtraction_impossible_at_observed_state`
* `source_simulation_and_ordered_subtraction_incompatible`

Object chain:

```
pinnedShape
→ accepted B1 global read store
→ immutable 5,646-instruction sourceProgram
→ public endpoints [0,12)
→ accepted initialState
→ repeated accepted E1Machine.step
→ first reachable subtraction underflow
```

Because the stop condition fires before route selection, no `HistoricalRouteCandidate`, allowed core, ROM/codec, target machine, charged lowering, reachable-width invariant, stuttering simulation, receipt, P/Q bridge, PASS/FAIL verdict, or expected-type route consumer is committed.

## Frozen choices and inputs

The six choices remain unchanged and unclaimed:

* `pinnedROMPC = 26`
* `pinnedTargetBranchPC = 5`
* `pinnedTargetArithmeticPhase = (26,0)`
* `pinnedTargetSubPhase = (32,0)`
* `pinnedMainRunReadIndex = 0`
* `pinnedProvenUnreadImageAddress = 693`

Accepted source identities:

* Source-port matrix: `4f8b3c84fbac5d8ef766b5d3df1c289c097fbeb3`
* Manifest: `7c6158bc212c96596187c997a3afb324c4537bcc`
* Topology: `b0fda017c2aafe7aca597b164892684cad6c4293`
* Correspondence: `5e18a2fcaf9aec36da45e773f668e7fdd272217e`
* Pinned fixture: `9544580d30eae8d86b3e5e903653e2799f0991cc`

## Verification

Passed:

* Project skill preflight at governance `a154983ae465b25ae6d8118b56abfa95ddf5b409`
* Focused committed obstruction build
* Direct executable probe with the exact seven-field observation
* Script syntax check
* Strict design-decision check
* Claim drift: 1,504 findings, zero strict failures
* Hygiene and native-decision scans
* Range and whitespace checks
* Exact two-commit path inventory
* Clean restoration/state

The committed obstruction replay passed its history, frozen-byte, immutable-source, and 42-case registry identity checks before its Lake subprocess attempted a network download. That subprocess was sandbox-blocked; the required escalation retry was denied by the platform usage limit. Therefore no terminal green replay or semantic mutation-campaign result is claimed.

## Architecture judgment required

A successor requires the coordinator to choose one:

1. Accept truncated/saturating subtraction and revise the no-wrap/cost contract.
2. Lower underflow through explicit comparison and branching, revising atomicity, ROM, simulation, and charge obligations.
3. Change and independently re-accept the historical source.

Plainly: the historical program intentionally uses `Nat` subtraction as a saturating min-chain operation. The proposed target contract forbids that behavior. A4 cannot consume B3 until this mismatch is resolved and a fresh B3 route is independently accepted.

Coordinator audit and architecture judgment are requested only. Nothing was pushed, merged, published, selected for A4, or called accepted.
