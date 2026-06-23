# Local BP Decoder Hardening Path

This is the post-capstone hardening plan for the only remaining live succinct
RMQ model caveat.

The concrete BP-native `2*n + o(n), O(1)` theorem is already in place:

```lean
RMQ.SuccinctFinal
  .builtRelativeSplitSparseExceptionBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile
```

The remaining caveat is local, not architectural.  The compact close directory
charges a constant BP-word window through:

```lean
localBPBlockWordsRead
localBPSameBlockCloseCosted
localBPLeftFringeCandidateCosted
localBPRightFringeCandidateCosted
ConcreteCompactBPCloseLCADirectory.lcaCloseCosted
```

but the three local helpers still compute their values with semantic BP
functions over `shape`, while charging the constant local word budget.  The
next target is to derive those local values from the charged words.

## Goal

Replace the semantic local helpers with decoded local helpers whose values are
computed from the same constant BP words already listed by
`localBPBlockWordsRead`, while preserving the existing final theorem names and
payload bounds.

Do not reopen the C1 false-close/select architecture, the compact interior
rmM navigator, or the final BP-native join unless the local-decoder target is
formally shown to be misspecified.

## Worker B Seeded Fringe Result

Worker B keeps the local decoder target positive but changes the interface from
"four BP words alone" to "four BP words plus an explicit base-excess seed":

```lean
localBPWindowBase
localBPWindowBits
localBPWindowGet?_eq_bpCode_get?
localBPSeedExcess
localBPSeedFromRankFalse
localBPSeedFromRankFalse_eq_localBPSeedExcess
localBPSeededExcessAt_eq_bpExcessAt
localBPLeftFringeCandidateSeededCosted_eq_semantic
localBPRightFringeCandidateSeededCosted_eq_semantic
```

The two seeded fringe helpers compute their candidates from the local window
bits and a seed, not by calling the old semantic helpers.  The equivalence
theorems require explicit coverage hypotheses for the endpoint fringe interval.
The minimal directory-interface delta is therefore: a compact close query must
also pass/read `localBPSeedExcess` at the window base, or equivalently pass/read
`Succinct.rankPrefix false shape.bpCode (localBPWindowBase ...)` and recover the
seed using `localBPSeedFromRankFalse`.

The current `ConcreteCompactBPCloseLCADirectory` interface still lists only
`localBPBlockWordsRead` for endpoint BP windows; it has no charged seed read.
Combined with `localBPWindowBits_alone_does_not_determine_base_excess`, this is
the formal reason the directory migration should wait for a seed-bearing read
surface instead of pretending the unseeded helper is decoded.

## Preferred Proof Shape

Use an equivalence-first migration:

1. Define a small local window view over the four BP words read by
   `localBPBlockWordsRead`.
2. Prove coverage: every BP bit needed by the same-block query or endpoint
   fringe query agrees with `shape.bpCode` at the corresponding global
   position.
3. Define decoded local versions of the three helpers:

   ```lean
   localBPSameBlockCloseDecodedCosted
   localBPLeftFringeCandidateDecodedCosted
   localBPRightFringeCandidateDecodedCosted
   ```

4. Prove helper equivalence:

   ```lean
   theorem localBPSameBlockCloseDecodedCosted_eq_semantic :
       (localBPSameBlockCloseDecodedCosted shape leftClose rightClose).erase =
         (localBPSameBlockCloseCosted shape leftClose rightClose).erase := ...

   theorem localBPLeftFringeCandidateDecodedCosted_eq_semantic :
       (localBPLeftFringeCandidateDecodedCosted shape blockSize leftClose).erase =
         (localBPLeftFringeCandidateCosted shape blockSize leftClose).erase := ...

   theorem localBPRightFringeCandidateDecodedCosted_eq_semantic :
       (localBPRightFringeCandidateDecodedCosted shape blockSize rightClose).erase =
         (localBPRightFringeCandidateCosted shape blockSize rightClose).erase := ...
   ```

5. Replace `ConcreteCompactBPCloseLCADirectory.crossBlockCloseCosted` and
   `ConcreteCompactBPCloseLCADirectory.lcaCloseCosted` to call the decoded
   helpers.
6. Reprove the existing profile theorem by rewriting through the equivalence
   lemmas:

   ```lean
   SuccinctCloseProposal.concreteCompactBPCloseLCADirectory_profile
   SuccinctFinal
     .builtRelativeSplitSparseExceptionBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile
   ```

The migration should keep the public capstone theorem names stable if
practical.  If a temporary sibling theorem is needed, it should be consumed back
into the existing public theorem before the loop stops.

## Decoder Guidance

The local decoder should be intentionally small.  It may be a pure reference
decoder over a bounded `List Bool` window; it does not need to introduce a new
RAM primitive or full machine interpreter.

Useful target definitions:

```lean
def localBPWindowBase
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) : Nat := ...

def localBPWindowBits
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) : List Bool := ...

def localBPWindowGet?
    (shape : Cartesian.CartesianShape)
    (blockSize close globalPos : Nat) : Option Bool := ...
```

Useful coverage theorem shape:

```lean
theorem localBPWindowGet?_eq_bpCode_get?
    {shape : Cartesian.CartesianShape}
    {blockSize close globalPos : Nat}
    (hcovered :
      localBPWindowBase shape blockSize close <= globalPos /\
        globalPos <
          localBPWindowBase shape blockSize close +
            4 * SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    localBPWindowGet? shape blockSize close globalPos =
      shape.bpCode[globalPos]? := ...
```

The hard arithmetic is expected to be:

- translating global close positions to offsets in the local window;
- handling partial final machine words by proving lookup equality only on
  covered in-range positions;
- showing the same-block slice and endpoint-fringe slices lie inside the
  four-word window under the canonical block-size regime already used by
  `ConcreteCompactBPCloseLCADirectory`;
- preserving the existing constant cost and machine-word read bounds.

## Stop Conditions

A worker should not stop after only adding decoder definitions, coverage lemmas,
or an equivalence theorem for one helper if the next helper or the directory
replacement is still obvious and inside its ownership.

A valid positive stop closes one of these named outcomes:

- decoded same-block, left-fringe, and right-fringe helpers all implemented and
  proved equivalent to the semantic helpers;
- `ConcreteCompactBPCloseLCADirectory` migrated to those decoded helpers with
  `concreteCompactBPCloseLCADirectory_profile` still proved; or
- the final BP-native capstone theorem reverified after the migration.

A valid negative stop requires a formal obstruction theorem showing that the
four-word local window is insufficient as stated, or that one of the proposed
theorem signatures is impossible.

## Worker Split

Use at most two write workers for the first pass.

Worker A owns decoder definitions and helper equivalence:

- `localBPWindowBase`, `localBPWindowBits`, `localBPWindowGet?`;
- decoded same-block and fringe helpers;
- the three `..._eq_semantic` equivalence theorems.

Worker B owns coverage, bounds, and integration:

- word-window coverage lemmas and partial-last-word lemmas;
- machine-word membership/bounds for the decoded query path;
- migration of `ConcreteCompactBPCloseLCADirectory` once Worker A's helper
  names are stable;
- final gate and documentation/status updates after the migration.

If Worker A has not landed the decoded helper interface yet, Worker B should
work on reusable coverage lemmas against the proposed names and avoid inventing
a competing decoder interface.
