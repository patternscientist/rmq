import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
KERNEL-CHECKED cross-shape statements (evidence class: kernel `rfl`, not
interpreter `#eval`).
-/

set_option maxHeartbeats 4000000

open RMQ RMQ.Cartesian RMQ.SuccinctFinal

namespace WQChecked2

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def shapesF : Nat -> Nat -> List CartesianShape
  | _, 0 => [CartesianShape.empty]
  | 0, _ => []
  | Nat.succ f, Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesF f k).flatMap fun l =>
          (shapesF f (n - k)).map fun r => CartesianShape.node l r

def shapes3 : List CartesianShape := shapesF 8 3
def shapes4 : List CartesianShape := shapesF 8 4
def shapes5 : List CartesianShape := shapesF 8 5

def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w
def addrStore (salt width : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range width).map fun b => ((seg * 131 + idx * 17 + salt) >>> b) % 2 == 1)

def st7 : WordRAM.ReadStore := addrStore 7 24
def stT : WordRAM.ReadStore := flatStore (List.replicate 16 true)
def stF : WordRAM.ReadStore := flatStore (List.replicate 16 false)

def wq (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s st l r

/-- TraceResult has no BEq instance; compare both projections. -/
def same (a b : WordRAM.TraceResult (Option Nat)) : Bool :=
  a.trace == b.trace && a.value == b.value

def real (s : CartesianShape) : WordRAM.ReadStore :=
  BPNavigation.concreteBPCloseNavigationGlobalReadStore s

def leftSpine5 : CartesianShape :=
  .node (.node (.node (.node (.node .empty .empty) .empty) .empty) .empty) .empty
def rightSpine5 : CartesianShape :=
  .node .empty (.node .empty (.node .empty (.node .empty (.node .empty .empty))))
def leftSpine4 : CartesianShape :=
  .node (.node (.node (.node .empty .empty) .empty) .empty) .empty
def rightSpine4 : CartesianShape :=
  .node .empty (.node .empty (.node .empty (.node .empty .empty)))

/-! ## (0) generator sanity -/

example : shapes3.length = 5 := by rfl
example : shapes4.length = 14 := by rfl
example : shapes5.length = 42 := by rfl
example : (shapes4.all (fun s => s.size == 4)) = true := by rfl
example : (shapes5.all (fun s => s.size == 5)) = true := by rfl

/-- The 42 shapes of size 5 have 42 PAIRWISE DISTINCT bpCodes. -/
example : ((shapes5.map (fun s => s.bpCode)).eraseDups.length == 42) = true := by rfl

/-- The two extremes really are the extremes. -/
example : leftSpine5.bpCode =
    [true, true, true, true, true, false, false, false, false, false] := by rfl
example : rightSpine5.bpCode =
    [true, false, true, false, true, false, true, false, true, false] := by rfl

/-! ## (1) ANTI-VACUITY: the controller is genuinely reply-driven.
     Cross-shape agreement would be worthless if the trace were a constant. -/

/-- Changing only the STORE changes the READ FOOTPRINT itself, not just the
    value: the controller's addresses are adaptive. -/
example : (same (wq leftSpine5 stF 0 5) (wq leftSpine5 stT 0 5)) = false := by rfl
example : (same (wq leftSpine5 st7 0 5) (wq leftSpine5 stT 0 5)) = false := by rfl

/-- Changing only the ENDPOINTS changes the result. -/
example : (same (wq leftSpine5 st7 0 5) (wq leftSpine5 st7 0 10)) = false := by rfl

/-- Under its OWN store each shape returns its own (different) RMQ answer, so
    the machinery is live and content-sensitive. -/
example : (wq leftSpine4 (real leftSpine4) 0 3).value = some 2 := by rfl
example : (wq rightSpine4 (real rightSpine4) 0 3).value = some 0 := by rfl

/-! ## (2) THE CLOSURE RESULT, kernel-checked.

     A shape queried against ANOTHER same-size shape's REAL store produces the
     OTHER shape's transcript and the OTHER shape's answer.  The semantic
     `shape` argument contributes nothing the store did not already supply. -/

example : wq rightSpine4 (real leftSpine4) 0 3 = wq leftSpine4 (real leftSpine4) 0 3 := by
  rfl
example : wq leftSpine4 (real rightSpine4) 0 3 = wq rightSpine4 (real rightSpine4) 0 3 := by
  rfl

/-- ALL 14 shapes of size 4 agree with the left spine when all are queried
    against `real leftSpine4`. -/
example :
    (shapes4.all fun a => same (wq a (real leftSpine4) 0 3) (wq leftSpine4 (real leftSpine4) 0 3))
      = true := by
  rfl

/-- Same against `real rightSpine4`. -/
example :
    (shapes4.all fun a => same (wq a (real rightSpine4) 0 3) (wq rightSpine4 (real rightSpine4) 0 3))
      = true := by
  rfl

/-! ## (3) exhaustive all-pairs under synthetic shape-free stores -/

/-- ALL 5 shapes of size 3, all 25 ordered pairs. -/
example :
    (shapes3.all fun a => shapes3.all fun b => same (wq a st7 0 3) (wq b st7 0 3)) = true := by
  rfl

/-- ALL 14 shapes of size 4, all 196 ordered pairs. -/
example :
    (shapes4.all fun a => shapes4.all fun b => same (wq a st7 0 4) (wq b st7 0 4)) = true := by
  rfl

/-- ALL 42 shapes of size 5, all 1764 ordered pairs. -/
example :
    (shapes5.all fun a => shapes5.all fun b => same (wq a st7 0 5) (wq b st7 0 5)) = true := by
  rfl

/-- Size 4 over 3 stores and 4 endpoint pairs: 14*14*3*4 = 2352 ordered checks. -/
example :
    ([(0, 4), (1, 3), (2, 2), (0, 8)].all fun lr =>
      [st7, stT, stF].all fun st =>
        shapes4.all fun a => shapes4.all fun b =>
          same (wq a st lr.1 lr.2) (wq b st lr.1 lr.2)) = true := by
  rfl

end WQChecked2
