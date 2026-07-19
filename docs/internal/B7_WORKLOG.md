# B7 Worklog - charged sparse-table level (worker B7-01)

Branch `claude/b7-charged-sparse-level`, worktree
`C:\Users\poin\Documents\RMQ\.worktrees\b7-charged-level`, base `f6564ec`.

## Milestone 0 - mechanism determination (this commit)

Finding re-verified at source at `f6564ec`; all four executed sites and
both underlying definitions confirmed. Full evidence, the rejected
alternatives, and the literal derivation are in DD-20260718-012
(`docs/internal/DESIGN_DECISIONS.md`). Summary:

- CHOSEN: mechanism 3, in a single-source single-read form. One new
  counted table `bpSparseLevelTable` over domain
  `macroSize + macroCount + 1`, cell `i` packing
  `Nat.log2 i * D + bpSparseLogSpan i`, unpacked by constant-divisor
  div/mod. One charged read per two-span call.
- The SPAN (`bpSparseLogSpan = 2 ^ Nat.log2`, `SparseArgMin.lean:598-599`)
  is part of the finding, not a separate issue - `Nat.pow` is a second
  Theta(log n) recursion at the same site. Charging only the level would
  not close the rung. This is why the stored cell is a packed pair.
- REJECTED 1 (already-charged read): the level forms the ADDRESS of the
  first read of the span, so it must be known before any charged read
  occurs; the reads present return a single `Option Nat` each.
- REJECTED 2 (widen an existing entry): one query needs the levels of
  three DIFFERENT runtime values on the cross-macro branch, so no single
  entry suffices; and the offset cell has ~1 spare bit.
- REJECTED 4 (restructure): indexing the sparse cell by span instead of
  level costs `n * macroSize` bits, i.e. Theta(n polylog), destroying o(n).
- NOT EVALUATED, per the user decision: an `msb`/`log2` ISA instruction,
  or weakening a bound to accept Theta(log n) work.

### Derived consequence: the route literal MOVES, 207 -> 210

Derived rather than assumed, from the exactly-tight chain
5 (`spanCandidateCosted_cost_le_five`) -> 10
(`twoSpanCandidateCosted_cost_le_ten`) -> 30
(`bpTwoLevelInteriorCandidateCosted_cost_le_thirty`, attained on the
cross-macro branch). One added read per two-span call gives 11 -> 33, and
`closeLCA = 2*11 + 2*37 + 33 = 129`,
`wholeQuery = 2*35 + 129 + 11 = 210`. B6 left 207 unmoved because its
recharged leaf was not on the maximizing branch; this one is.

### Corroboration

DD-20260718-011 (E1-R4m, tail of `DESIGN_DECISIONS.md`) independently
flagged the same `Nat.log2` / `2 ^ Nat.log2` computation as an open
ISA-level item and explicitly did not decide it. This entry decides the
route side of it.

### Recorded for the uncharged-computation inventory, not relied on here

`summaryCosted` (`RelativeSummary.lean:735-754`) charges four reads;
`bpRelativeSummaryMinCandidate`
(`EndpointFringe/PrefixRange/RelativeSummaryCandidate.lean:15-22`) never
projects the `maxRel` field. One of the four reads is dead at the
min-candidate site. Dropping it would take the span cap 5 -> 4, the
two-span cap 10 -> 8, and the interior cap to 24, so the B7 read would
fit under the existing 30 and the literal would NOT move. This was NOT
adopted: it changes shared summary machinery used by max-candidate
consumers, its blast radius is far outside this rung, and it is an
optimization rather than the charged-level fix. Flagged for coordinator
adjudication.

## Verification ledger

- Baseline `lake build RMQ` at `f6564ec`: launched under the
  `Global\RMQHeavyVerification` mutex; result recorded at the next commit.
