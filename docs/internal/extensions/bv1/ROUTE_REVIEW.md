# BV-1 independent reader route review

Mode: read-only construction/contract review of the working feasibility source;
not the mandatory final blind exact-commit candidate audit. Base/governance
0e6a00f654abc64f8b68988fa9675b9a839dca2f. Reviewer: independent physical-inventory
agent. Reviewed SelectExperiment.lean, ReaderInterface.lean, CONTRACT.md and
the frozen matrix, without editing or running Lean. Compilation was supplied
evidence rather than independently repeated.

No concrete canonical-reader counterexample was found. No acceptance verdict
for the full target follows. The following are source-grounded proof duties.

1. GenericReaderMetadata fixes only target register3 and width register22;
   no hidden shape/readiness premise was found. Source overwrites scratch
   before use and keeps writes within the proposed frame [8194,8271).
2. genericReaderReceipts is a canonical expected trace. Empty supplied memory
   with target=false, segment0 faults at the first descriptor load (address23)
   with one receipt, while that expected specification lists four descriptor
   receipts. CanonicalGenericReaderCorrect fixes Experiment.memory bits and
   is not refuted. Arbitrary-memory fault/agreement evidence must use actual
   execution, retaining early fault and decoded-reply dependence.
3. First-word-length stride is not valid for an arbitrary bounded array:
   `#[[], [true]]` at index1 produces an empty span. Prove presence, exact
   flatten-slice recovery, length and global base recovery for each canonical
   ofChunks/ofChunksWithSentinel/fixed-width table builder. A maximum word
   length and payload erasure alone are insufficient. Short initial words
   and all trailing empty sentinels require explicit cases.
4. True-target packet `2^len-decoded` matches the proved finite normalization
   identity; present empty words yield packet1, missing words yield packet0.
   Only segment0 changes. Flags11/15 and common tables retain their original
   values. Still prove equality of the shared raw word array across both
   canonical target builders and normalization of the whole supplied-store
   controller, rather than only the final List specification.
5. Header mapping appears consistent:23 scalar words, two92-word descriptor
   banks, body at207*W; raw bits once, each target's16 components, four absent
   segments and two common chunk tables. Setup count is independent of n
   geometry. Exact offsets/metadata installation remain proof obligations.
6. The actual regularLocateBlock, spanBlock, selectCloseBlock and compiler
   are reused. Source evaluation still needs to compose through the generic
   reader into the same primitive run, with all positivity/eight-chunk/strict
   word bounds and both exceptional routes. No shared Packed edit was needed.

The lead updated CONTRACT.md to the actual elaborated names and the two
noncanonical counterexample boundaries. These findings neither prove the
reader nor negate the frozen BV-1 target. Final route disposition belongs to
the coordinator after reading the committed source and execution evidence.
