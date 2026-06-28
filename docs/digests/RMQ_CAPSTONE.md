# RMQ Capstone Digest

Snapshot: 2026-06-28. This note digests the stable RMQ theorem stack. It is
not the fast-moving rank/select or union-find frontier; those now have separate
digests.

## What Changed Conceptually

The RMQ capstone is no longer just "we have several exact RMQ algorithms." The
verified story now connects four layers in one public surface:

1. The reference problem is a half-open, leftmost range-minimum query over
   `List Int`.
2. Cartesian shape determines all RMQ answers, so values can be replaced by a
   shape representative.
3. Cartesian shapes require almost `2*n` bits to distinguish, via Catalan
   counting.
4. A balanced-parentheses code of exact length `2*n`, plus `o(n)` auxiliary
   navigation payload, answers every valid query in constant modeled time.

The short public alias is:

```lean
#check RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery
```

It abbreviates the construction-heavy theorem
`RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile`.

## Plain English Proof Map

Range-minimum query asks for the leftmost index of the minimum value in an
interval. The first move is to freeze that contract. In Lean, the core names
are `RMQ.LeftmostArgMin`, `RMQ.CandidateExact`, `RMQ.RMQBackend`, and the useful
backend agreement theorem `RMQ.RMQBackend.queryBuilt_eq`.

The second move is a structural one: the exact values in the array are not
needed after preprocessing. The Cartesian tree shape remembers enough order
information to answer every RMQ query. The bridge to LCA is checked through
`RMQ.Cartesian.certifiedReduction` and
`RMQ.RMQToLCAReduction.queryWithLCABackend_sound`.

The third move is a counting lower bound. The public lower-bound alias

```lean
#check RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack
```

expands to
`RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack`.
It says exact RMQ state encodings must have enough bitstrings to distinguish
Cartesian shapes. The reader-facing arithmetic is the doubled integer form
`4*n - (3*log2(2*n+1)+3) <= 2*bits`, corresponding to
`2n - 1.5 log n - O(1)` without rational arithmetic in the Lean statement.

The fourth move is the succinct upper bound. A Cartesian shape has a balanced
parentheses code of length `2*n`. The final query uses false-select to map
query endpoints to close positions, a compact BP close/LCA directory to find
the answer close, and false-rank to map back to an inorder index. The exactness
bridge is `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQQueryCosted_exact`.

## Live Assumptions

- Constant time is a model claim in `Costed` and `RAM.Exec`, not a claim about
  Lean's native execution.
- Payload bits are the BP code plus counted auxiliary bits. Proof certificates
  and invariants are not payload unless a payload view counts them.
- Indexed table reads and bounded word primitives are charged as unit-cost
  operations under the repository model.
- The theorem is a checked formalization of a known data-structure story, not
  a new asymptotic data-structure result.

## Anti-Oracle Check

The abstraction to watch is
`RMQ.SuccinctFinal.BPCloseAccessDirectory`: by itself it is a compatibility
surface with costed fields. The public theorem does not stop at an arbitrary
inhabitant of that surface. It uses the concrete
`RMQ.SuccinctFinal.builtGenericSparseExceptionSelectBPCloseAccessFamily` and
the profile
`RMQ.SuccinctFinal.builtGenericSparseExceptionSelectBPCloseAccessFamily_profile`.

The warning label is
`RMQ.SuccinctSelect.chargedSelectPositionSource_allows_empty_select_oracle`.
It records that a charged-looking interface can still be too weak if exactness
comes from a callback rather than charged payload. A parallel BP warning is
`RMQ.SuccinctClose.payloadLiveBPRelativeRmmInteriorDirectory_profile_allows_proof_only_oracle`.

## Skeptical Grad Student Questions

**Is the lower bound a runtime lower bound?**

No. It is a fixed-length payload capacity theorem from Cartesian-shape
counting. It does not say a RAM query must take many steps.

**Why can values disappear?**

Because the Cartesian shape preserves the leftmost RMQ behavior of the
representative arrays. The final exactness statement compares to
`scanWindow shape.representative left len`.

**Where exactly is the query cost paid?**

In model-level costed operations: select endpoint closes, run BP close/LCA
navigation, then rank the answer close back to an inorder index.

**What remains open for RMQ itself?**

The main `2*n + o(n), O(1)` modeled capstone is landed. Remaining RMQ work is
presentation polish, especially a flatter payload-only statement, not a hidden
correctness blocker.

