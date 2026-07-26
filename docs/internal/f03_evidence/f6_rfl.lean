import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
Kernel-CHECKED (not `#eval`) shape-independence witnesses for controller
leaf L1 at a FIXED shape-free store.  If `rfl` closes these, the two
same-size shapes produce definitionally identical trace AND value.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace F6Rfl

def noiseStore (salt : Nat) : WordRAM.ReadStore where
  readWord? segment index :=
    some ((List.range 16).map fun k =>
      (salt + segment * 7919 + index * 104729 + k * 1299709) % 3 == 0)

def leaf (shape : CartesianShape) (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  concreteBPNativeSelectCloseGlobalWordTraceResultWithStore shape store idx

/-- size 2, right spine -/
def s2R : CartesianShape :=
  CartesianShape.node CartesianShape.empty
    (CartesianShape.node CartesianShape.empty CartesianShape.empty)
/-- size 2, left spine -/
def s2L : CartesianShape :=
  CartesianShape.node
    (CartesianShape.node CartesianShape.empty CartesianShape.empty)
    CartesianShape.empty

/-- size 3, right spine -/
def s3R : CartesianShape := CartesianShape.node CartesianShape.empty s2R
/-- size 3, left spine -/
def s3L : CartesianShape := CartesianShape.node s2L CartesianShape.empty
/-- size 3, balanced -/
def s3B : CartesianShape :=
  CartesianShape.node
    (CartesianShape.node CartesianShape.empty CartesianShape.empty)
    (CartesianShape.node CartesianShape.empty CartesianShape.empty)

set_option maxHeartbeats 2000000

example : leaf s2R (noiseStore 11) 0 = leaf s2L (noiseStore 11) 0 := rfl
example : leaf s2R (noiseStore 11) 1 = leaf s2L (noiseStore 11) 1 := rfl
example : leaf s2R (noiseStore 11) 2 = leaf s2L (noiseStore 11) 2 := rfl

example : leaf s3R (noiseStore 11) 0 = leaf s3L (noiseStore 11) 0 := rfl
example : leaf s3R (noiseStore 11) 1 = leaf s3B (noiseStore 11) 1 := rfl
example : leaf s3L (noiseStore 11) 2 = leaf s3B (noiseStore 11) 2 := rfl

example :
    leaf s3R (concreteBPNativeSuccinctRMQGlobalReadStore s3R) 1 =
      leaf s3L (concreteBPNativeSuccinctRMQGlobalReadStore s3R) 1 := rfl

end F6Rfl
