# V1 manuscript/source relationship

The manuscript deliberately cites the query-theorem subset at
`3849ecbb53bbedfcd679352cc68d095fa5a304c2`. Its line citations continue to name
that tree. The V1 implementation starts from
`ee44f04a561f2194b3713f071c26b6faf9ba7fab` and preserves those mathematical
statements. The release manifest, rather than this document, identifies the
eventual candidate commit without a self-referential source pin.

The source comparison between those two commits found three modified files
in the transitive `RMQPaper` import closure. `SparseLevelWidth.lean` adds
`@[macro_inline]` to two concrete witness definitions;
`ReviewerReachabilitySmall.lean` adds it to three private witness states;
`RMQ/Headlines/RMQ.lean` corrects “straight-line” to “loop-free” in a docstring.
The declaration types and computational bodies are unchanged. New construction,
optimization, lifecycle, native and bitvector modules are additive and outside
that narrow paper closure. The declaration-check script adds the three packed
query names required by the already present paper row; this repairs its coverage.

The V1 proof maintenance additionally reuses existing generic rank/select lemmas,
removes an unused private helper, and names an exact trace-bind decomposition.
The public theorem signatures, machine definitions and cost constants remain
unchanged. The checked client examples consume those existing statements.
Candidate validation must run the paper checker, declaration inventory, public
root build, axiom inventories and integrated gate; their actual outcomes and
source identity belong in the V1 verification record, not in an assumed result
here. The pinned paper citation checker continues to inspect the historical
source lines rather than mistaking shifted current lines for broken citations.

The manuscript covers the reference contract, succinct query upper bound,
fixed-length lower bound, charged trace, packed cell-probe and primitive-query
models. Its preprocessing limitation now explicitly concerns that subset.
The newer continuous construction and reusable-owner result is described in
the [artifact claims packet](../artifact/CLAIMS.md) and
[lifecycle proof guide](../docs/digests/LIFECYCLE_PROOF_GUIDE.md), with distinct
native-runtime assumptions and evidence status. No lifecycle theorem is silently
inserted into the paper's old pin or its `ACCEPTED_BASE` ledger rows.

This is an intentional scope boundary, not a claim that the current repository
lacks construction results. Existing historical verification entries remain
dated records; they are not restamped as V1 checks.
