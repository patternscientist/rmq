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

def succinctClassicPayloadTruePositions (xs : List Int) : List Nat :=
  (RMQ.SuccinctClassic.buildPayload xs).zipIdx.filterMap fun bitAndIdx =>
    if bitAndIdx.1 then some bitAndIdx.2 else none

#guard (RMQ.SuccinctClassic.buildPayload ([] : List Int)).length == 561

#guard (RMQ.SuccinctClassic.buildPayload ([7] : List Int)).length == 10708

#guard (RMQ.SuccinctClassic.buildPayload ([7] : List Int)).take 16 ==
  [true, false, false, false, false, false, false, false,
    false, true, false, false, false, false, false, true]

#guard succinctClassicPayloadTruePositions ([7] : List Int) ==
  [0, 9, 15, 24, 30, 59, 71]

#guard succinctClassicPayloadTruePositions ([2, 1] : List Int) ==
  [0, 1, 15, 22, 36, 42, 50, 77, 129, 164]

#guard succinctClassicPayloadTruePositions ([1, 1] : List Int) ==
  [0, 2, 15, 22, 35, 42, 50, 77, 128, 164]

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

example :
    (RMQ.SuccinctClassic.buildPayload tinyRMQInput).length =
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
