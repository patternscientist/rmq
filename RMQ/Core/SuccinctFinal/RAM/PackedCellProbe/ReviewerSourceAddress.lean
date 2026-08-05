import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerProbe

/-!
# Where each live access source sits in the consumed payload

`SourceFactorization.lean` gives `packedSourceFlatOffset`, the shape-free bit offset
of a source inside the **flat** payload. The consumed payload has a different
layout, so it needs its own offset function, and that is what this module builds.

## Why the offset is a prefix sum rather than a component table

The flat layout groups sources into components and offsets them componentwise. The
reviewer layout does not: its access half is literally

```
concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources.flatMap
  (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape)
```

so a source's offset is the summed length of everything before it in that one list.
Defining it as `takeWhile (· != source)` over the canonical list -- rather than as a
table of eighteen constants -- means the offset cannot drift from the payload it
measures: both read the same list.

## The one thing that makes the prefix sum size-only

`selectSparseRelative` is the only live access source without a size-only bit
length, and in the canonical list it is **last**. Every proper prefix therefore
consists of counted sources alone, so `packedReviewerAccessOffset` is a function of
`n` and `longCount` with no unit-stride hypothesis anywhere -- unlike the payload's
total length, which needs one precisely because the sparse table is included in it.

That ordering is load-bearing and not obviously deliberate, so
`packedReviewerAccessPrefix_counted` pins it: it fails if the sparse relative table
is ever moved earlier in the list.

## What this module does not establish

* Nothing here reads a word. This locates a source's payload; slicing an indexed
  word out of it, and probing cells for that slice, come after.
* The close half's sources are not offset here. They sit past the access half and
  are reached through `packedReviewerPayload_interiorSlice` instead.
-/

namespace RMQ

namespace SuccinctFinal

namespace PackedCellProbe

open RMQ.Cartesian

/-! ### Two general list facts -/

/-- The length of a `flatMap` is the summed length of its parts. -/
private theorem packedFlatMapPrefixLength {alpha beta : Type} (f : alpha -> List beta) :
    forall pre : List alpha,
      (pre.flatMap f).length = (pre.map (fun x => (f x).length)).sum := by
  intro pre
  induction pre with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, ih]

/--
**A `flatMap` part is the slice at its prefix sum.** Given a split of the source
list around `a`, the image of `a` is exactly the window of the flattened list that
starts where the prefix ends and runs for `(f a).length` bits.
-/
private theorem packedFlatMapSliceOfSplit {alpha beta : Type} (f : alpha -> List beta)
    (pre post : List alpha) (a : alpha) :
    (((pre ++ a :: post).flatMap f).drop
        ((pre.map (fun x => (f x).length)).sum)).take (f a).length = f a := by
  rw [List.flatMap_append, List.flatMap_cons,
    ← packedFlatMapPrefixLength f pre, List.drop_left, List.take_left]

/--
The same fact against a list given by an equation rather than syntactically split.
Stated separately because the list also occurs inside the prefix sum, so rewriting
the goal with the split would rewrite both occurrences; discharging the equation
inside the lemma avoids that.
-/
private theorem packedFlatMapSliceOfEq {alpha beta : Type} (f : alpha -> List beta)
    (l pre post : List alpha) (a : alpha) (hl : l = pre ++ a :: post) :
    ((l.flatMap f).drop ((pre.map (fun x => (f x).length)).sum)).take
        (f a).length = f a := by
  subst hl
  exact packedFlatMapSliceOfSplit f pre post a

/-- The part named by a split ends no later than the end of the flattened list. -/
private theorem packedFlatMapPrefixFits {alpha beta : Type} (f : alpha -> List beta)
    (pre post : List alpha) (a : alpha) :
    (pre.map (fun x => (f x).length)).sum + (f a).length <=
      ((pre ++ a :: post).flatMap f).length := by
  rw [List.flatMap_append, List.flatMap_cons,
    ← packedFlatMapPrefixLength f pre, List.length_append, List.length_append]
  omega

private theorem packedFlatMapPrefixFitsOfEq {alpha beta : Type}
    (f : alpha -> List beta) (l pre post : List alpha) (a : alpha)
    (hl : l = pre ++ a :: post) :
    (pre.map (fun x => (f x).length)).sum + (f a).length <= (l.flatMap f).length := by
  subst hl
  exact packedFlatMapPrefixFits f pre post a

/--
**A list splits at the first occurrence of a member.** The `takeWhile` prefix used
by the offset below is exactly the part before that occurrence.

Stated at the concrete source type rather than generically: the generic form would
have to name a `BEq` instance alongside `DecidableEq`, and the two need not be the
same instance as the one `!=` elaborates to in the definition below.
-/
private theorem packedSplitAtFirst
    (a : ConcreteBPNativeSuccinctRMQFlatPayloadSource) :
    forall l : List ConcreteBPNativeSuccinctRMQFlatPayloadSource, a ∈ l ->
      exists post, l = l.takeWhile (fun x => x != a) ++ a :: post := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons x xs ih =>
      intro h
      by_cases hx : x = a
      · refine ⟨xs, ?_⟩
        subst hx
        simp
      · have hmem : a ∈ xs := by
          rcases List.mem_cons.mp h with heq | hmem
          · exact absurd heq.symm hx
          · exact hmem
        obtain ⟨post, hpost⟩ := ih hmem
        refine ⟨post, ?_⟩
        have htw :
            (x :: xs).takeWhile (fun y => y != a) =
              x :: xs.takeWhile (fun y => y != a) := by
          simp [hx]
        rw [htw, List.cons_append]
        exact congrArg (List.cons x) hpost

/-! ### The offset -/

/--
The bit offset of a live access source inside the reviewer access half: the summed
bit length of every source before it in the canonical list.

Shape-free by construction -- it takes only `n` and the header's `longCount`.
-/
def packedReviewerAccessOffset (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) : Nat :=
  ((concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources.takeWhile
      (fun x => x != source)).map (packedSourceBitLength n longCount)).sum

/--
The bit offset of a live access source inside the whole consumed payload: past the
balanced parenthesis code, then into the access half.
-/
def packedReviewerSourceOffset (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) : Nat :=
  2 * n + packedReviewerAccessOffset n longCount source

/--
**The sparse relative table is last.** Every proper prefix of the canonical live
access list consists of counted sources, so every prefix sum above is size-only.

This is checked by evaluation over all twenty-nine source constructors. Moving
`selectSparseRelative` earlier in the canonical list breaks it.

Membership is a genuine hypothesis, not decoration: for a source that is not in the
list at all -- every flat-only source, and the close half's -- `takeWhile` consumes
the whole list, sparse relative table included, and the conclusion is false.
`decide` reports exactly that for the eleven such constructors when `hmem` is
dropped.
-/
theorem packedReviewerAccessPrefix_counted
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hmem :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources)
    (hne :
      source != ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative) :
    forall s,
      s ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources.takeWhile
          (fun x => x != source) ->
        s != ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative := by
  revert hmem hne
  cases source <;> decide

/--
On a prefix of counted sources the actual payload lengths are the size-only ones,
so the prefix sum computes the real offset.
-/
private theorem packedReviewerPrefixLength_eq
    (shape : CartesianShape) :
    forall pre : List ConcreteBPNativeSuccinctRMQFlatPayloadSource,
      (forall s, s ∈ pre ->
        s != ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative) ->
      (pre.map (fun x =>
          (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape x).length)).sum =
        (pre.map (packedSourceBitLength shape.size (longCount shape))).sum := by
  intro pre
  induction pre with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro hall
      have hx :
          x != ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative :=
        hall x (by simp)
      have hrest :
          forall s, s ∈ xs ->
            s !=
              ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative := by
        intro s hs
        exact hall s (List.mem_cons_of_mem _ hs)
      simp only [List.map_cons, List.sum_cons]
      rw [packedSourceBitLength_eq shape x hx, ih hrest]

/-! ### The access half -/

/--
**A source's payload is the window of the access half at its offset.** No
unit-stride hypothesis: the prefix consists of counted sources only.
-/
theorem packedReviewerAccessPayload_slice
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hmem :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources)
    (hne :
      source != ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative) :
    ((concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape).drop
        (packedReviewerAccessOffset shape.size (longCount shape) source)).take
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length =
      concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source := by
  obtain ⟨post, hsplit⟩ :=
    packedSplitAtFirst source
      concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources hmem
  have hpre :=
    packedReviewerPrefixLength_eq shape _
      (packedReviewerAccessPrefix_counted source hmem hne)
  unfold concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload
    packedReviewerAccessOffset
  rw [← hpre]
  exact packedFlatMapSliceOfEq _ _ _ post source hsplit

/--
The source's window is inside the access half.

Proved from the split rather than from `packedReviewerAccessPayload_slice`. The
slice equation alone does **not** give this: a source with an empty payload
satisfies it at every offset, including offsets past the end of the list, so
`min 0 (len - off) = 0` carries no information about `off`.
-/
theorem packedReviewerAccessOffset_fits
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hmem :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources)
    (hne :
      source != ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative) :
    packedReviewerAccessOffset shape.size (longCount shape) source +
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length <=
      (concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape).length := by
  obtain ⟨post, hsplit⟩ :=
    packedSplitAtFirst source
      concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources hmem
  have hpre :=
    packedReviewerPrefixLength_eq shape _
      (packedReviewerAccessPrefix_counted source hmem hne)
  unfold concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload
    packedReviewerAccessOffset
  rw [← hpre]
  exact packedFlatMapPrefixFitsOfEq _ _ _ post source hsplit

/-! ### The whole consumed payload -/

/--
**The consumed payload, past the balanced parenthesis code, is the access half then
the close half.** The counterpart of `packedReviewerPayload_drop_closeOffset` one
component earlier.
-/
theorem packedReviewerPayload_drop_bpCode (shape : CartesianShape) :
    (packedReviewerPayloadBits shape).drop shape.bpCode.length =
      concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape ++
        (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload ++
          (SuccinctClose.bpFringeChunkTable
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload ++
            (SuccinctClose.bpChunkSelectTable
              (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false).payload := by
  unfold packedReviewerPayloadBits
    concreteBPNativeSuccinctRMQCanonicalReviewerPayload
    concreteBPNativeSuccinctRMQCanonicalReviewerPayloadLayout
  dsimp only
  rw [show
      shape.bpCode ++
            concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape ++
          (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload ++
            (SuccinctClose.bpFringeChunkTable
              (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload ++
              (SuccinctClose.bpChunkSelectTable
                (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false).payload =
        shape.bpCode ++
          (concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape ++
            (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload ++
              (SuccinctClose.bpFringeChunkTable
                (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload ++
                (SuccinctClose.bpChunkSelectTable
                  (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
                  false).payload) by
    simp [List.append_assoc]]
  exact List.drop_left

/--
**A live access source's payload is the window of the consumed payload at its
shape-free offset.**

This is the reviewer counterpart of
`concreteBPNativeSuccinctRMQFlatPayloadSource_flat_slice`, and the address surface
the physical read over `packedReviewerMemory` consumes.
-/
theorem packedReviewerPayload_accessSlice
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hmem :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources)
    (hne :
      source != ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative) :
    ((packedReviewerPayloadBits shape).drop
        (packedReviewerSourceOffset shape.size (longCount shape) source)).take
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length =
      concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source := by
  have hbp : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  have hfits := packedReviewerAccessOffset_fits shape source hmem hne
  unfold packedReviewerSourceOffset
  -- `List.drop_drop` splits `l.drop (X + Y)` into `(l.drop X).drop Y`, outer summand
  -- first, so the offset is already in the order this needs. Normalising the sum
  -- first would produce the reversed nesting.
  rw [← hbp, ← List.drop_drop, packedReviewerPayload_drop_bpCode shape,
    show
        concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape ++
              (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload ++
            (SuccinctClose.bpFringeChunkTable
              (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload ++
              (SuccinctClose.bpChunkSelectTable
                (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
                false).payload =
          concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape ++
            ((SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload ++
              (SuccinctClose.bpFringeChunkTable
                (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload ++
                (SuccinctClose.bpChunkSelectTable
                  (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
                  false).payload) by
      simp [List.append_assoc]]
  rw [packedPrefixSlice _ _ hfits]
  exact packedReviewerAccessPayload_slice shape source hmem hne

end PackedCellProbe

end SuccinctFinal

end RMQ
