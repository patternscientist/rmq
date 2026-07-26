import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL stage 7: turn the same-size controller experiment into a CHECKED
statement rather than an `#eval` printout, using the REAL `shapesOfSize`
enumerator from RMQ/Core/Shape.lean:1228 (whose completeness is proved there by
`mem_shapesOfSize_iff_shapeOfSize`, Shape.lean:1324).  So the quantifier is
"every Cartesian shape of this size", not "the shapes I happened to build".
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace AdvSZDecide

def st : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 12).map fun j => ((seg * 7 + idx * 13 + j * 5) % 3 == 0))

def fp (s : CartesianShape) (l r : Nat) : List (Nat × Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore s st l r

def ov (s : CartesianShape) (l r : Nat) : Option Nat :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    s st l r).value

/-- Same-size invariance of the ordered read footprint AND the output value,
    over EVERY Cartesian shape of size 4, for three endpoint pairs. -/
theorem sameSize4 :
    ((shapesOfSize 4).all fun s =>
        ((fp s 0 4 == fp (CartesianShape.node CartesianShape.empty
            (CartesianShape.node CartesianShape.empty
              (CartesianShape.node CartesianShape.empty
                (CartesianShape.node CartesianShape.empty
                  CartesianShape.empty)))) 0 4) &&
         (fp s 1 3 == fp (CartesianShape.node CartesianShape.empty
            (CartesianShape.node CartesianShape.empty
              (CartesianShape.node CartesianShape.empty
                (CartesianShape.node CartesianShape.empty
                  CartesianShape.empty)))) 1 3) &&
         (ov s 0 4 == ov (CartesianShape.node CartesianShape.empty
            (CartesianShape.node CartesianShape.empty
              (CartesianShape.node CartesianShape.empty
                (CartesianShape.node CartesianShape.empty
                  CartesianShape.empty)))) 0 4))) = true := by
  native_decide

/-- ANTI-VACUITY, also checked: the enumerator really is nontrivial and the
    footprint really is nonempty. -/
theorem enum4_nontrivial : (shapesOfSize 4).length = 14 := by native_decide

theorem fp4_nonempty :
    0 < (fp (CartesianShape.node CartesianShape.empty
          (CartesianShape.node CartesianShape.empty
            (CartesianShape.node CartesianShape.empty
              (CartesianShape.node CartesianShape.empty
                CartesianShape.empty)))) 0 4).length := by native_decide

/-- ANTI-VACUITY, checked: bpCode content genuinely differs inside size 4. -/
theorem codes4_differ :
    ((shapesOfSize 4).map fun s => s.bpCode).eraseDups.length = 14 := by
  native_decide

#print axioms sameSize4
#print axioms enum4_nontrivial
#print axioms codes4_differ

end AdvSZDecide
