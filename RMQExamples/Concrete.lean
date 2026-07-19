import RMQ.Core.Window
import RMQ.Core.Succinct
import RMQ.Core.SuccinctRMQClassic
import RMQ.Core.UnionFind

/-!
# Tiny executable examples

These examples are intentionally small. They give downstream readers concrete
terms to build before they inspect the larger theorem aliases.
-/

namespace RMQ.Examples.Concrete

example : RMQ.scanWindow ([5, 2, 7, 1, 3] : List Int) 1 3 = 3 := by
  rfl

example : RMQ.Succinct.rankPrefix true [true, false, true, true] 3 = 2 := by
  rfl

example : RMQ.Succinct.select false [true, false, true, false] 1 = some 3 := by
  rfl

def tinyRMQInput : List Int := [3, 1, 4, 1, 5]

inductive CanonicalQueryRoute where
  | invalid
  | sameBlock
  | crossBlock
deriving Repr, DecidableEq, BEq

/-- Executable inspection of the actual canonical close/LCA branch. -/
def canonicalQueryRoute
    (xs : List Int) (left right : Nat) : CanonicalQueryRoute :=
  if _hvalid : RMQ.ValidRange xs left right then
    let shape := RMQ.SuccinctClassic.cartesianShape xs
    match RMQ.SuccinctSpace.bpCloseOfInorder? shape left,
        RMQ.SuccinctSpace.bpCloseOfInorder? shape (right - 1) with
    | some leftClose, some rightClose =>
        let blockSize :=
          RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape
        if RMQ.SuccinctClose.blockOfClose blockSize leftClose =
            RMQ.SuccinctClose.blockOfClose blockSize rightClose then
          .sameBlock
        else
          .crossBlock
    | _, _ => .invalid
  else
    .invalid

/-- Canonical physical store with the first actually consumed word removed. -/
def dropFirstConsumedPhysicalWord
    (xs : List Int) (left right : Nat) : RMQ.WordRAM.ReadStore :=
  let canonical := RMQ.SuccinctClassic.reviewerPhysicalReadStore xs
  let first? :=
    (RMQ.SuccinctClassic.reviewerPhysicalFootprint xs left right).head?
  { readWord? := fun segment address =>
      if segment == 0 && some address == first? then none
      else canonical.readWord? segment address }

/-- Executable positional backing check for every physical read, including
failed reads at the checked dead address. -/
def physicalReadsMatchCanonicalStore
    (xs : List Int) (left right : Nat) : Bool :=
  let result :=
    RMQ.SuccinctClassic.reviewerPhysicalTraceResult xs left right
  let words := RMQ.SuccinctClassic.reviewerPhysicalWords xs
  result.trace.all fun event =>
    match event with
    | RMQ.WordRAM.TraceEvent.readWord segment address word? =>
        segment == 0 && words[address]? == word?
    | _ => true

#guard
  (RMQ.SuccinctClassic.buildPayload tinyRMQInput).length <=
    2 * tinyRMQInput.length +
      RMQ.SuccinctClassic.overhead tinyRMQInput.length

#guard
  RMQ.SuccinctSpace.flattenPayloadWords
      (RMQ.SuccinctClassic.reviewerPhysicalWords tinyRMQInput) ==
    RMQ.SuccinctClassic.buildPayload tinyRMQInput

#guard RMQ.SuccinctClassic.queryCost == 210
#guard RMQ.SuccinctClassic.canonicalSilentSparseLevelQueryCost == 207
#guard RMQ.SuccinctClassic.canonicalSilentWordRankSelectQueryCost == 142
#guard RMQ.SuccinctClassic.canonicalSilentFringeQueryCost == 76

#guard RMQ.SuccinctClassic.canonicalTransitionalQueryCost == 328

#guard canonicalQueryRoute tinyRMQInput 2 4 == .sameBlock

#guard canonicalQueryRoute tinyRMQInput 0 5 == .crossBlock

#guard canonicalQueryRoute tinyRMQInput 1 1 == .invalid

#guard (RMQ.SuccinctClassic.queryCosted tinyRMQInput 0 5).erase == some 1

#guard (RMQ.SuccinctClassic.queryCosted tinyRMQInput 2 4).erase == some 3

#guard (RMQ.SuccinctClassic.queryCosted ([4, 4, 5] : List Int) 0 2).erase ==
  some 0

#guard (RMQ.SuccinctClassic.queryCosted ([5, 4, 4] : List Int) 0 3).erase ==
  some 1

#guard (RMQ.SuccinctClassic.queryCosted ([8, 6, 7, 6, 9] : List Int) 1 4).erase ==
  some 1

#guard (RMQ.SuccinctClassic.queryCosted ([8, 6, 7, 6, 9] : List Int) 2 5).erase ==
  some 3

#guard (RMQ.SuccinctClassic.queryCosted ([9, 8, 7] : List Int) 1 1).erase ==
  none

#guard (RMQ.SuccinctClassic.queryCosted ([9, 8, 7] : List Int) 2 1).erase ==
  none

#guard (RMQ.SuccinctClassic.queryCosted ([9, 8, 7] : List Int) 0 4).erase ==
  none

#guard
  (RMQ.SuccinctClassic.reviewerPhysicalTraceResult
    ([9, 8, 7] : List Int) 1 1).value == none

#guard
  (RMQ.SuccinctClassic.reviewerPhysicalTraceResult
    ([9, 8, 7] : List Int) 1 1).trace == []

#guard
  (RMQ.SuccinctClassic.reviewerPhysicalTraceResult
    ([7] : List Int) 0 1).value == some 0

#guard
  (RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
    ([7] : List Int)
    (dropFirstConsumedPhysicalWord ([7] : List Int) 0 1) 0 1).value == none

#guard physicalReadsMatchCanonicalStore ([7] : List Int) 0 1

/- The one guarded story supplies the same none/empty/zero packet for each
public invalid-range shape, including every caller-supplied physical store. -/
example :
    RMQ.SuccinctClassic.queryTraceResult ([9, 8, 7] : List Int) 1 1 =
        RMQ.WordRAM.TraceResult.pure none /\
      RMQ.SuccinctClassic.reviewerPhysicalTraceResult
          ([9, 8, 7] : List Int) 1 1 = RMQ.WordRAM.TraceResult.pure none /\
      RMQ.SuccinctClassic.queryCosted ([9, 8, 7] : List Int) 1 1 =
        RMQ.Costed.pure none /\
      RMQ.SuccinctClassic.reviewerPhysicalFootprint
          ([9, 8, 7] : List Int) 1 1 = [] /\
      forall store : RMQ.WordRAM.ReadStore,
        RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
            ([9, 8, 7] : List Int) store 1 1 =
          RMQ.WordRAM.TraceResult.pure none := by
  exact RMQ.SuccinctClassic.flatPayloadStoreNoSyntheticExecutionStory_invalid_semantics
    ([9, 8, 7] : List Int) 1 1 (by decide)

example :
    RMQ.SuccinctClassic.reviewerPhysicalTraceResult
        ([9, 8, 7] : List Int) 2 1 =
      RMQ.WordRAM.TraceResult.pure none := by
  exact
    (RMQ.SuccinctClassic.flatPayloadStoreNoSyntheticExecutionStory_invalid_semantics
      ([9, 8, 7] : List Int) 2 1 (by decide)).2.1

example :
    RMQ.SuccinctClassic.reviewerPhysicalFootprint
        ([9, 8, 7] : List Int) 0 4 = [] := by
  exact
    (RMQ.SuccinctClassic.flatPayloadStoreNoSyntheticExecutionStory_invalid_semantics
      ([9, 8, 7] : List Int) 0 4 (by decide)).2.2.2.1

example :
    (RMQ.SuccinctClassic.buildPayload tinyRMQInput).length <=
      2 * tinyRMQInput.length +
        RMQ.SuccinctClassic.overhead tinyRMQInput.length := by
  exact RMQ.SuccinctClassic.buildPayload_length tinyRMQInput

example :
    (RMQ.SuccinctClassic.queryCosted tinyRMQInput 0 5).erase =
      some (RMQ.scanWindow tinyRMQInput 0 5) := by
  simpa using
    (RMQ.SuccinctClassic.queryCosted_exact
      tinyRMQInput (left := 0) (len := 5)
      (by decide) (by decide))

example :
    RMQ.SuccinctClassic.FlatPayloadStoreNoSyntheticExecutionStory
      tinyRMQInput 0 5 := by
  exact
    RMQ.SuccinctClassic.flatPayloadStoreNoSyntheticExecutionStory
      tinyRMQInput 0 5

def tinyUnionFind : RMQ.UnionFind.State where
  size := 3
  repr := fun x => x
  repr_lt := by
    intro x hx
    exact hx

example : tinyUnionFind.find? 1 = some 1 := by
  simp [tinyUnionFind, RMQ.UnionFind.State.find?]

example : tinyUnionFind.find? 4 = none := by
  simp [tinyUnionFind, RMQ.UnionFind.State.find?]

end RMQ.Examples.Concrete
