import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! Minimal KERNEL-CHECKED core: the two statements that carry the argument.
    Evidence class = kernel `rfl`, not interpreter `#eval`. -/

set_option maxHeartbeats 2000000

open RMQ RMQ.Cartesian RMQ.SuccinctFinal

namespace WQChecked3

def addrStore (salt width : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range width).map fun b => ((seg * 131 + idx * 17 + salt) >>> b) % 2 == 1)
def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w

def st7 : WordRAM.ReadStore := addrStore 7 24
def stT : WordRAM.ReadStore := flatStore (List.replicate 16 true)

def wq (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s st l r

def real (s : CartesianShape) : WordRAM.ReadStore :=
  BPNavigation.concreteBPCloseNavigationGlobalReadStore s

/-- bpCode = true^4 false^4 -/
def L4 : CartesianShape :=
  .node (.node (.node (.node .empty .empty) .empty) .empty) .empty
/-- bpCode = (true false)^4 -/
def R4 : CartesianShape :=
  .node .empty (.node .empty (.node .empty (.node .empty .empty)))

example : L4.size = 4 := by rfl
example : R4.size = 4 := by rfl
example : L4.bpCode = [true, true, true, true, false, false, false, false] := by rfl
example : R4.bpCode = [true, false, true, false, true, false, true, false] := by rfl

/-! ANTI-VACUITY: the controller is reply-driven, so agreement is not trivial. -/

/-- Under their OWN stores the two shapes give DIFFERENT answers. -/
example : (wq L4 (real L4) 0 3).value = some 2 := by rfl
example : (wq R4 (real R4) 0 3).value = some 0 := by rfl

/-- Changing only the store changes the trace. -/
example : ((wq L4 st7 0 4).trace == (wq L4 stT 0 4).trace) = false := by rfl

/-! THE CLOSURE RESULT.  A shape queried against the OTHER shape's REAL store
    produces the OTHER shape's entire TraceResult -- trace and value.  The
    semantic `shape` argument contributes nothing beyond what the store supplies. -/

example : wq R4 (real L4) 0 3 = wq L4 (real L4) 0 3 := by rfl
example : wq L4 (real R4) 0 3 = wq R4 (real R4) 0 3 := by rfl
example : wq R4 (real L4) 1 3 = wq L4 (real L4) 1 3 := by rfl
example : wq L4 (real R4) 1 3 = wq R4 (real R4) 1 3 := by rfl

/-! Same under a synthetic shape-free store. -/

example : wq L4 st7 0 4 = wq R4 st7 0 4 := by rfl
example : wq L4 stT 0 4 = wq R4 stT 0 4 := by rfl
example : wq L4 st7 2 3 = wq R4 st7 2 3 := by rfl

end WQChecked3
