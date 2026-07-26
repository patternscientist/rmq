import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! HEADER-SCHEMA part B: the 9 interior component offsets (segment 20 layout). -/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctClose

namespace HdrB

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def leftSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (leftSpine n) .empty

def rightSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node .empty (rightSpine n)

partial def balanced : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (balanced (n / 2)) (balanced (n - n / 2))

def cliff (n : Nat) : CartesianShape :=
  .node (leftSpine (n / 2)) (rightSpine (n - n / 2 - 1))

def offs (s : CartesianShape) : List Nat :=
  let o := canonicalRelativeRmmInteriorComponentOffsets s
  [o.baseline, o.minRel, o.maxRel, o.argOffset, o.localOffset,
   o.globalBlock, o.localLevel, o.globalLevel, o.deadAddress]

def go (n : Nat) : String :=
  let L := offs (leftSpine n)
  let R := offs (rightSpine n)
  let B := offs (balanced n)
  let C := offs (cliff n)
  s!"n={n} L={L}\n     R={R}\n     B={B}\n     C={C}\n     allAgree={L = R && L = B && L = C}"

#eval IO.println (go 384)
#eval IO.println (go 512)

end HdrB
