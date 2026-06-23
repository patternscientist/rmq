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

but the local helpers still compute some values with semantic BP functions over
`shape`, while charging the constant local word budget.  The endpoint-fringe
side now has a seeded decoder tied to the charged word reads by
`localBPWindowBits_eq_flatten_localBPBlockWordsRead`; the compact directory
passes explicit rank-false seeds through
`localBPSeedFromRankFalseCosted_eq_localBPSeedExcess` and consumes the seeded
left/right fringe helpers.  The remaining local caveat is the same-block helper,
not the cross-block endpoint-fringe path.

## Goal

Replace the remaining semantic local-helper uses with decoded helpers whose
values are computed from the same constant BP words already listed by
`localBPBlockWordsRead`, plus an explicitly charged base-excess/rank-false
seed where the obstruction theorem shows such a seed is necessary. Preserve the
existing final theorem names and payload bounds.

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

## Completed Endpoint-Fringe Proof Shape

The endpoint-fringe migration used this equivalence-first path:

1. The proof-facing window now agrees with the charged reads. The local slice
   used by `localBPWindowBits` is exactly the flattened consecutive chunk reads
   from `localBPBlockWordsRead`.

   ```lean
   theorem localBPWindowBits_eq_flatten_localBPBlockWordsRead :
       localBPWindowBits shape blockSize close =
         SuccinctSpace.flattenPayloadWords
           (localBPBlockWordsRead shape blockSize close) := ...
   ```

2. The seed-bearing read surface is a charged rank-false read at
   `localBPWindowBase`, converted by:

   ```lean
   localBPSeedFromRankFalse_eq_localBPSeedExcess
   ```

3. `ConcreteCompactBPCloseLCADirectory.crossBlockCloseCosted` now uses a
   seed-bearing version that calls:

   ```lean
   localBPLeftFringeCandidateSeededCosted
   localBPRightFringeCandidateSeededCosted
   ```

   and consumes:

   ```lean
   localBPLeftFringeCandidateSeededCosted_eq_semantic
   localBPRightFringeCandidateSeededCosted_eq_semantic
   ```

4. The existing profile theorem is reproved by rewriting through the seeded
   equivalence lemmas:

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

The remaining hard arithmetic is expected to be:

- translating global close positions to offsets in the local window;
- handling partial final machine words by proving lookup equality only on
  covered in-range positions;
- showing the endpoint-fringe slices lie inside the four-word window under the
  canonical block-size regime already used by
  `ConcreteCompactBPCloseLCADirectory`;
- proving the `localBPWindowBits` view is read from the charged
  `localBPBlockWordsRead` payload words, not just from an uncharged direct
  `shape.bpCode.drop`;
- threading the seed read through the directory without hiding an uncharged
  `bpExcessAt`/`rankPrefix` computation;
- preserving the existing constant cost and machine-word read bounds.

## Stop Conditions

A worker should not stop after only adding decoder definitions, coverage lemmas,
or a seed-field/interface hook if the next directory migration theorem is still
obvious and inside its ownership.  For the endpoint-fringe slice, the bridge and
directory migration are now closed; future local-decoder work should target the
same-block helper or a payload-only encoding presentation.

A valid positive stop closes one of these named outcomes:

- the charged-window bridge from `localBPBlockWordsRead` to `localBPWindowBits`
  is proved and consumed by the seeded fringe path;
- `ConcreteCompactBPCloseLCADirectory` is migrated to seed-bearing fringe
  helpers with
  `concreteCompactBPCloseLCADirectory_profile` still proved; or
- the final BP-native capstone theorem reverified after the migration.

A valid negative stop requires a formal obstruction theorem showing that the
charged local word window plus the explicit seed is insufficient as stated, or
that one of the proposed theorem signatures is impossible.

## Worker Split

This is now best handled by one integration worker. Parallelize only if the
lead worker pins exact theorem names for a read-window bridge and a seed-read
adapter that can be proved independently without touching
`ConcreteCompactBPCloseLCADirectory`.
