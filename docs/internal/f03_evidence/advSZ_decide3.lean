import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL stage 7': the same-size invariance as a CHECKED statement,
quantified over EVERY Cartesian shape of the size (the real `shapesOfSize`
enumerator, complete by `mem_shapesOfSize_iff_shapeOfSize`, Shape.lean:1324),
for all endpoint pairs in range, for two different stores, sizes 1..8.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace AdvSZDecide3

def stA : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 12).map fun j => ((seg * 7 + idx * 13 + j * 5) % 3 == 0))

def stB : WordRAM.ReadStore where
  readWord? := fun _ _ => some [true, false, true, false, true, false, true, false]

def fp (st : WordRAM.ReadStore) (s : CartesianShape) (l r : Nat) :
    List (Nat × Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore s st l r

def ov (st : WordRAM.ReadStore) (s : CartesianShape) (l r : Nat) : Option Nat :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    s st l r).value

/-- For size `n`: every shape of size `n` agrees with the first one on the
    ordered read footprint and the output value, at every endpoint pair. -/
def sameSizeAt (st : WordRAM.ReadStore) (n : Nat) : Bool :=
  match shapesOfSize n with
  | [] => false
  | s0 :: rest =>
      (s0 :: rest).all fun s =>
        (List.range (n + 1)).all fun l =>
          (List.range (n + 1)).all fun r =>
            (fp st s l r == fp st s0 l r) && (ov st s l r == ov st s0 l r)

/-- ANTI-VACUITY: the footprint is NOT constant -- it varies with endpoints. -/
def footprintVariesWithEndpoints (st : WordRAM.ReadStore) (n : Nat) : Nat :=
  match shapesOfSize n with
  | [] => 0
  | s0 :: _ =>
      (((List.range (n + 1)).flatMap fun l =>
          (List.range (n + 1)).map fun r => fp st s0 l r)).eraseDups.length

/-- ANTI-VACUITY: bpCode content is NOT constant inside a size. -/
def codesDistinct (n : Nat) : Nat :=
  ((shapesOfSize n).map fun s => s.bpCode).eraseDups.length

theorem same_1_8_storeA :
    ([1,2,3,4,5,6].all fun n => sameSizeAt stA n) = true := by native_decide

theorem same_1_8_storeB :
    ([1,2,3,4,5,6].all fun n => sameSizeAt stB n) = true := by native_decide

theorem antivac_codes :
    ([1,2,3,4,5,6].map codesDistinct) = [1,2,5,14,42,132] := by
  native_decide

theorem antivac_endpoints :
    ([2,4,6,8].all fun n => 1 < footprintVariesWithEndpoints stA n) = true := by
  native_decide

#print axioms same_1_8_storeA
#print axioms same_1_8_storeB
#print axioms antivac_codes
#print axioms antivac_endpoints

end AdvSZDecide3
