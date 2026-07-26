import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! Offsets/layout size-congruence ACROSS the ACTIVE threshold (defender measured
    the relative-summary activity predicate first flips true at n = 512).
    Cheap content probe so this terminates. -/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctClose

namespace AdvRxOff512

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

partial def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (leftSpine n) CartesianShape.empty

partial def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node CartesianShape.empty (rightSpine n)

partial def balanced : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (balanced (n / 2)) (balanced (n - n / 2))

def family (n : Nat) : List (String × CartesianShape) :=
  [("leftSpine", leftSpine n), ("rightSpine", rightSpine n), ("balanced", balanced n)]

def layoutTuple (s : CartesianShape) : Nat × Nat × Nat × Nat :=
  let l := RelativeRmm.canonicalLayout s
  (l.blockSize, l.blocksPerSuper, l.blockCount, l.relativeWidth)

def cheapContent (s : CartesianShape) : List Nat :=
  (List.range 8).map (fun p => bpExcessAt s (p * 7))

#eval show IO Unit from do
  for n in [200, 256, 512, 600] do
    let fam := family n
    match fam with
    | [] => pure ()
    | (_, s0) :: _ =>
      let o0 := canonicalRelativeRmmInteriorComponentOffsets s0
      let lt0 := layoutTuple s0
      let c0 := cheapContent s0
      let mut offD := 0
      let mut layD := 0
      let mut conD := 0
      for (_, s) in fam do
        if canonicalRelativeRmmInteriorComponentOffsets s != o0 then offD := offD + 1
        if layoutTuple s != lt0 then layD := layD + 1
        if cheapContent s != c0 then conD := conD + 1
      IO.println s!"n={n} ACTIVE={decide (canonicalBPRelativeMinMaxArgSummaryTableActive s0)} layout={lt0} offsets.deadAddress={o0.deadAddress} | layoutDiffers={layD} offsetsDiffers={offD} | ANTIVAC contentDiffers={conD}"

end AdvRxOff512
