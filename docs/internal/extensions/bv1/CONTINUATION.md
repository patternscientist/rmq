# BV-1 implementation continuation

Entry HEAD: 645a0502b9da9ad6444edbe44759e1c2c5661f25, clean, on the existing
codex/bv-1-fully-charged-rank-select branch. Original governance/base:
0e6a00f654abc64f8b68988fa9675b9a839dca2f. Canonical preflight passed with
rmq-proof-sprint required and actual runtime catalog rmq-audit-prompt,
rmq-coordinator, rmq-proof-sprint. The frozen matrix remains byte-for-byte
unchanged; current evidence is appended in separate records.

The coordinator approved the one-raw-input, two-directory, charged segment-zero
normalization route. This is a proof architecture decision, not acceptance of
any composed target. Full target and all inherited invariants remain required.

## Next theorem interfaces and consumers

The regular-layout worker proves exact first-stride slice recovery for every
actual component in Experiment.memory, including trailing empty sentinels.
The lead proves descriptor installation from that same memory and source
evaluation using actual regularLocateBlock and spanBlock. Their join is exactly
CanonicalGenericReaderCorrect in ReaderInterface.lean, whose quantifiers and
canonical-memory boundary are unchanged.

MemoryLayout.lean will expose the existing experiment's component list, header
banks and body by definitional equality. Descriptor lookup must identify the
component's prefix bit offset, total bit length, first word length and count.
The span recovery consumer fixes the same header/body allocation and physical
width. Empty logical words may have positions beyond the end of serialized
bits and cause no read; absent words retain the descriptor lookup but return
the absent packet. No arbitrary-memory correctness follows from these
canonical lookup facts.

The controller reviewer identifies the minimal generic metadata and supplied
store proof layer for the unchanged SelectSource/RankSource. Mathematical
normalization alone is not controller refinement. The lead consumes the
review's exact signatures after the physical reader bridge.

## Verification coverage

Development checks build each new owned module and its direct typed consumer
with the existing owned-process wrapper, unique stage ID, one Lean job and a
180-second initial deadline for warm imported modules. The closest earlier
proof checks took 8–19 seconds; a cold new dependency closure gets its own
observed-progress schedule. No unchanged expensive command is retried after
timeout. Only the lead allocates the shared build slot.

These checks cover REQ-BV-REUSE, INV-STORE-IDENTITY, INV-VALUE-DEPENDENCY,
INV-READ-BACKING and INV-GLOBAL-PHYSICAL-MACHINE at their reader components;
full-target rows remain open until consumed in the capstone. Final verification
retains both original-base and continuation-base range checks. A full gate
slot will be requested only on a frozen full candidate.

Crossing registry version 3 preserves reader-component-crossing and adds
raw-false-crossing and raw-true-crossing. The new pair uses the same length-511
alternating input and raw logical word index 19. Its 9-bit span crosses a
176-bit physical cell; the true-target control additionally requires that the
expected packet differs from the raw packet. Every case checks the actual
second-load instruction, evaluated address and backing reply. Startup and the
new true-target selector precede the full exact three-case registry. These are
reader-component controls, not whole-select reachability witnesses. Execution
results remain pending until recorded by the owned command wrapper.

## Composition details retained during implementation

The rank extension can use the four reserved logical segments without changing
the select protocol: append the four Jacobson sample tables after the current
35 body components; select the target's super/block tables in segments 17/18;
use segment 19 as a sentinel-bearing alias of the already stored raw bits; keep
segment 20 absent. The raw alias has independent logical count but the same
payload bit range, and is not complemented. Rank's in-word target remains its
actual Boolean argument. A supplied-store select refinement is generalized
only over agreement on its actual segments below 17 and 21/22, preserving the
existing canonical result as an exact consumer. This prepares one shared
allocation without retaining a second raw input.

An empty sentinel needs no payload lookup, but regularLocateBlock still
computes its nominal bit position. Source safety must bound that numeric
position, including sentinel indices, even when the decode theorem correctly
permits it beyond the serialized body's bit length. Address bounds at actual
loads and bounds on arithmetic results are separate obligations.
