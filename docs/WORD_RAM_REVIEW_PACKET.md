# Word-RAM Review Packet

Snapshot: 2026-07-01. This packet is a focused reviewer note for the
first-order Word-RAM refinement boundary used by the interpreted RMQ and
rank/select theorem surfaces.

It is deliberately narrower than `docs/TRUST_AUDIT_PACKET.md`: it asks whether
the interpreted theorem path can hide answers in proof-only fields or
uncharged callbacks.

## Threat Model

The model should support this claim:

- a query program reads explicit payload words from a `WordRAM.Store`;
- the model cost is the length of the interpreter trace;
- every word-read event in the trace records the exact value returned by the
  store; and
- if two stores answer every read the same way, then the interpreted result and
  trace are identical.

That is the small anti-oracle property. It does not make the project a compiled
machine-code proof, but it does rule out the main shallow-model failure mode:
proof certificates or callback fields silently deciding the answer while the
trace pretends to do constant-time payload reads.

## Core Definitions

The boundary lives in `RMQ/Core/WordRAM.lean`.

- `WordRAM.Store` is the payload-memory interface. Its relevant operation is
  `Store.readWord? segment index`.
- `WordRAM.Program ty` is a first-order query program over a small instruction
  set: word reads, fixed-width decoders, sampled rank, and word-local select.
- `WordRAM.Program.eval program store` returns a value and a trace.
- `WordRAM.Result.toCosted` projects the interpreted result into the ordinary
  `Costed` layer used by the rest of the repository.

## Formal Safeguards

The following theorems are the reviewer-facing checks for the boundary.

```lean
RMQ.WordRAM.Program.eval_toCosted_cost_eq_trace_length
RMQ.WordRAM.Program.eval_reads_subset_payload
RMQ.WordRAM.Program.eval_readWord_event_eq_store
RMQ.WordRAM.Program.eval_readWord_address_mem
RMQ.WordRAM.Program.eval_event_read_or_primitive
RMQ.WordRAM.Program.eval_no_zero_cost_control
RMQ.WordRAM.Program.eval_word_reads_length_le_machine
RMQ.WordRAM.Program.eval_eq_of_readWord_eq
RMQ.WordRAM.Program.eval_toCosted_eq_of_readWord_eq
RMQ.WordRAM.Register.NatExpr.eval_fitsInBits_of_noOverflow
RMQ.WordRAM.Register.RegProgram.eval_event_address_fitsInBits
RMQ.WordRAM.Register.NatProgram.eval_event_address_fitsInBits
```

Read in plain English:

- `eval_toCosted_cost_eq_trace_length`: the `Costed` cost is exactly the trace
  length, not a separately asserted number.
- `eval_reads_subset_payload`: every word read in the trace came from the
  payload store.
- `eval_readWord_event_eq_store`: a concrete read event reports exactly
  `store.readWord? segment index`.
- `eval_readWord_address_mem`: a read event's address occurs in the
  first-order program syntax; it is not supplied by a proof callback.
- `eval_event_read_or_primitive` and `eval_no_zero_cost_control`: every trace
  event is either a payload read or a word-local primitive, and zero-cost
  control never appears as a charged trace event.
- `eval_word_reads_length_le_machine`: if the store is word-bounded, every
  returned word in the trace is machine-word-bounded.
- `eval_eq_of_readWord_eq`: a program cannot distinguish two stores with the
  same read interface.
- `eval_toCosted_eq_of_readWord_eq`: the same extensionality holds after
  projecting to `Costed`.
- `Register.NatExpr.NoOverflow` and its helper theorems: arithmetic is
  interpreted as mathematical `Nat`; machine-word safety is an explicit
  side condition, not implicit wraparound.
- `Register.{RegProgram,NatProgram}.eval_event_address_fitsInBits`: when the
  selected first-order read addresses fit the declared machine-bit bound, every
  read event in the interpreted trace has a bounded segment and index.

The interpreted public theorem surfaces checked by the focused script include:

```lean
RMQ.RankSelect.compressedFIDFixedWeightInterpretedFamilyProfile
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQQueryInterpretedCosted_refines_queryCosted
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQQueryInterpretedCosted_exact
RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_interpreted_profile
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_refines_queryInterpretedCosted
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_exact
RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted_refines_wholeQueryInterpretedCosted
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted_exact
RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_leaf_trace_profile
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted_refines_wholeQueryInterpretedCosted
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted_exact
RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_word_trace_profile
RMQ.Headlines.rankSelectCompressedFIDFixedWeightInterpretedFamilyProfile
RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryInterpreted
RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryLeafTrace
RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryWordTrace
```

## Reproduction Commands

Focused check:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\review_wordram.ps1
```

The script builds the interpreter and public interpreted roots, runs the
focused axiom check, performs hygiene scans, and runs `git diff --check`.

Raw axiom print:

```powershell
lake env lean scripts\wordram_axiom_check.lean
```

Full repository gate:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\gate.ps1
```

The full gate now also runs `scripts/wordram_axiom_check.lean`.

## Non-Claims

This packet does not claim:

- Lean's runtime for lists, arrays, or structures has the modeled runtime;
- the query has been compiled into one complete machine-code program;
- the first-order instruction set contains every possible word-RAM operation;
- all historical bridge-backed components have been flattened into a single
  AST; or
- `Program.pure` by itself is a public anti-oracle theorem endpoint.

The current claim is more precise: the public interpreted capstones route their
rank/select/close leaves through first-order `WordRAM.Program` bridge layers,
and the checked interpreter lemmas make the payload-read and trace-cost
provenance explicit.  The RMQ capstone now goes one rung further: the outer
query is a closed whole-query control program that stores intermediate
close-select and LCA-close answers in registers before invoking the two-level
register-backed rank leaf.

## Whole-Query Program Frontier

The interpreted RMQ capstone now has two layers:

- the older leaf-interpreted theorem, where close-select, rank-close, and
  compact close/LCA table reads are each routed through `WordRAM.Program`, then
  sequenced by Lean-level `Costed.bind`; and
- the newer whole-query theorem, where that sequencing is represented by the
  closed `SuccinctFinal.WholeQueryProgram` instruction list.

The first register/control-flow rung now exists in
`RMQ/Core/WordRAM/Register.lean`, with a consumed dynamic-address theorem in
`RMQ/Core/SuccinctSpace/BPCloseLCARegisterRAM.lean`.  That theorem replaces the
small handoff from optional endpoint-close registers to a BP close/LCA table
read by a first-order register program.  The same register module also now has
natural-valued programs for dynamic stored-word rank, including the two-level
sampled-rank case used by the final BP-native RMQ capstone. It also carries the
bounded-register/address vocabulary: values fit a declared bit width via
`FitsInBits`, expressions advertise `NoOverflow`, and selected read addresses
prove `AddressFitsInBits` before the event-level theorem transfers that fact to
the interpreted trace. There is no silent modular arithmetic policy in this
layer; overflow safety is a proof obligation.

The whole-query theorem is the first closed one-program statement for the final
RMQ query. The final query is not straight-line: the two close-select results
determine the compact close/LCA lookup, and that answer-close result determines
the final rank query. The `WholeQueryProgram` layer records that control flow
with first-order instructions and explicit optional/natural registers.

The tempting shortcut to avoid is a generic higher-order continuation such as
`bind : Program Nat -> (Nat -> Program ty) -> Program ty`. In Lean that stores
an arbitrary function inside the syntax tree, which reopens the oracle-shaped
gap this layer was built to close. The next stronger design should keep the
syntax first-order: registers, fixed arithmetic/address instructions, option
tests, and payload-read operations, with the same read-provenance and
machine-word-bound theorems as the current `Program.eval` boundary. The current
core/register interpreters already prove the first part of this discipline:
every read address comes from syntax under the current register file, while
branching and register arithmetic remain zero-cost control and never appear as
information-bearing trace events.

The final `answerClose + 1` rank query is now routed through
`SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterInterpretedCosted`,
which refines the earlier interpreted rank query while computing the super
sample, block sample, and bit-word addresses from a register expression. The
current all-size word-trace theorem flattens the outer query controller to one
`WordRAM.TraceEvent` stream. Its close-select leg, answer-rank leg, and
compact-close rank-seed reads are structural payload/register traces. The
all-size execution-story theorem
`RMQ.Headlines.succinctRMQGlobalPayloadStoreExecutionStory` adds the global
store/provenance layer for that stream: each event is a payload read or bounded
word primitive, and each read agrees with one concrete global payload store.
`RMQ.Headlines.succinctRMQGlobalPayloadStoreBoundedExecutionStory` adds the
current finite-width hardening: every payload-read address and every natural
operand/result exposed by word-local primitives fits a trace-local bit width.
Tiny/inactive close-navigation fallback work is represented as the fixed
synthetic `TraceResult.costOnlyTrace` primitive marker rather than payload
reads. The large-regime companion adds the explicit `2^128 <= shape.size`
premise and routes the compact close/LCA leg through structural
local/fringe/interior trace replay. Remaining hardening is tighter
component-level machine-word side conditions, structural replacement of
fallback markers where possible, and reuse of the same style across
rank/select, BP navigation, and future machine-model surfaces.

## Large-File Cleanup Note

The initial rank/select facade split has landed. `RMQ/Core/RankSelectCompressed.lean`
and `RMQ/Core/RankSelectPublic.lean` are now stable barrels over role modules.
A current line-count audit points to these largest follow-up candidates:

- `RMQ/Core/RankSelectCompressed/Base.lean`;
- `RMQ/Core/RankSelectPublic/Profiles.lean`;
- `RMQ/Core/UnionFind/Forest.lean`;
- larger close-navigation role files under `RMQ/Core/SuccinctClose/`.

The Word-RAM layer itself is already small and role-local. The right next
module-split cleanup is therefore not to split `WordRAM`, but to continue
extracting rank/select and union-find role modules behind stable public barrels.
