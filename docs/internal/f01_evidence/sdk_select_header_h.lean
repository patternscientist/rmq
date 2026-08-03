import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
EG-CP-F01, part H: is `selSparseRelative` actually empty below the crossover?

`localIsSparseException` = `(! superIsLong ...) && (wordBits < shortSuperLocalSpan)`.
Below the crossover `superIsLong` is always false, so the FIRST conjunct is
SATISFIED, not blocked.  The long-table argument therefore does NOT transfer.
Measure the actual sparse-exception popcount at reachable sizes.
-/

namespace SdkH

open RMQ
open RMQ.Cartesian
open RMQ.GenericSelect

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def leftSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (leftSpine n) .empty

def rightSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node .empty (rightSpine n)

def cliff (n : Nat) : CartesianShape :=
  .node (leftSpine (n / 2)) (rightSpine (n - n / 2 - 1))

def row (name : String) (s : CartesianShape) : String :=
  let bits := s.bpCode
  let n := bits.length
  let longCount :=
    RMQ.Succinct.rankPrefix true (longSuperFlagBits bits false)
      (superSlotCount bits false)
  let sparseCount :=
    RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits bits false)
      (localSlotCount bits false)
  let longLen := (longSuperRelativeTable bits false).payload.length
  let sparseLen := (sparseExceptionRelativeTable bits false).payload.length
  s!"  {name} size={s.size} n={n} longSupers={longCount} longLen={longLen}" ++
    s!" sparseExc={sparseCount} sparseLen={sparseLen}" ++
    s!" [budgets long={longSuperRelativeTableOverhead n}" ++
    s!" sparse={sparseExceptionRelativeTableOverhead n}]"

def go (k : Nat) : String :=
  String.intercalate "\n"
    [ s!"size={k}"
    , row "leftSpine " (leftSpine k)
    , row "rightSpine" (rightSpine k)
    , row "cliff     " (cliff k) ]

#eval IO.println (go 16)
#eval IO.println (go 64)
#eval IO.println (go 256)

end SdkH
