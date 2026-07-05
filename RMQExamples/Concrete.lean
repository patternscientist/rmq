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
