import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import RMQ.Core.SuccinctRMQClassic

open RMQ
open RMQ.SuccinctFinal
open RMQ.Cartesian

namespace DPF2Smoke

def lb {a b : Type} (l : List a) (f : a -> List b) : List b :=
  l.foldr (fun x acc => f x ++ acc) []

def shapesF : Nat -> Nat -> List CartesianShape
  | 0, _ => []
  | _ + 1, 0 => [CartesianShape.empty]
  | f + 1, n + 1 =>
      lb (List.range (n + 1)) (fun k =>
        lb (shapesF f k) (fun l =>
          (shapesF f (n - k)).map (fun r => CartesianShape.node l r)))

def shapes (n : Nat) : List CartesianShape := shapesF (n + 1) n

#eval (shapes 0).length
#eval (shapes 1).length
#eval (shapes 2).length
#eval (shapes 3).length
#eval (shapes 4).length
#eval (shapes 5).length
#eval (shapes 6).length
#eval ((shapes 5).map CartesianShape.size).eraseDups
#eval ((shapes 5).map (fun s => s.bpCode)).eraseDups.length

def storeConst : WordRAM.ReadStore where
  readWord? _ _ := some [true, false, true, true, false, false, true, false]

#eval (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        (CartesianShape.node CartesianShape.empty CartesianShape.empty)
        storeConst 17 1).value

-- the real per-shape memory image
#eval ((concreteBPNativeSuccinctRMQGlobalReadStore
        (CartesianShape.node CartesianShape.empty CartesianShape.empty)).readWord? 17 0)

end DPF2Smoke
