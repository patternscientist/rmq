import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
KERNEL-CHECKED cross-shape statements.

Everything else in this campaign is `#eval` output: the Lean INTERPRETER printed
a number.  This file states the same facts as propositions and discharges them
by `rfl`, so the KERNEL checks them.  Strictly stronger evidence class.

`shapesOfSize` is fuel-recursive (structural) so the kernel can unfold it.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal

namespace WQChecked

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

/-- All Cartesian shapes of size `n`, given enough fuel.  Structural recursion
    on the fuel, so it reduces in the kernel. -/
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

def wq (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s st l r

def st7 : WordRAM.ReadStore := addrStore 7 24
def stT : WordRAM.ReadStore := flatStore (List.replicate 16 true)
def stF : WordRAM.ReadStore := flatStore (List.replicate 16 false)

/-! ### (0) generator sanity -/

example : shapes3.length = 5 := by rfl
example : shapes4.length = 14 := by rfl
example : shapes5.length = 42 := by rfl
example : (shapes4.all (fun s => s.size == 4)) = true := by rfl
example : (shapes5.all (fun s => s.size == 5)) = true := by rfl

/-! ### (0b) ANTI-VACUITY.  Without these, agreement below would prove nothing. -/

/-- The 42 shapes of size 5 have 42 PAIRWISE DISTINCT bpCodes: the sweep really
    does range over maximally different tree contents at fixed size. -/
example : ((shapes5.map (fun s => s.bpCode)).eraseDups.length == 42) = true := by rfl

/-- Changing the STORE changes the trace, so probe replies really do steer the
    controller; agreement across shapes is not agreement of a constant function. -/
example :
    ((wq shapes5.head! stF 0 5).trace == (wq shapes5.head! stT 0 5).trace) = false := by
  rfl

/-- Changing the ENDPOINTS changes the trace. -/
example :
    ((wq shapes5.head! st7 0 5).trace == (wq shapes5.head! st7 1 3).trace) = false := by
  rfl

/-! ### (1) pointwise: left spine vs right spine at size 5.
     bpCode = true^5 false^5   versus   (true false)^5
     -- maximally different bit distributions at equal size. -/

def leftSpine5 : CartesianShape :=
  .node (.node (.node (.node (.node .empty .empty) .empty) .empty) .empty) .empty
def rightSpine5 : CartesianShape :=
  .node .empty (.node .empty (.node .empty (.node .empty (.node .empty .empty))))

example : leftSpine5.bpCode =
    [true, true, true, true, true, false, false, false, false, false] := by rfl
example : rightSpine5.bpCode =
    [true, false, true, false, true, false, true, false, true, false] := by rfl

/-- Whole-query TraceResult is DEFINITIONALLY EQUAL for the two extreme shapes. -/
example : wq leftSpine5 st7 0 5 = wq rightSpine5 st7 0 5 := by rfl
example : wq leftSpine5 stT 2 4 = wq rightSpine5 stT 2 4 := by rfl
example : wq leftSpine5 stF 0 10 = wq rightSpine5 stF 0 10 := by rfl

/-! ### (2) exhaustively quantified all-pairs checks -/

/-- ALL 5 shapes of size 3, all 25 ordered pairs, one store, one endpoint pair. -/
example :
    (shapes3.all fun a => shapes3.all fun b => wq a st7 0 3 == wq b st7 0 3) = true := by
  rfl

/-- ALL 14 shapes of size 4, all 196 ordered pairs. -/
example :
    (shapes4.all fun a => shapes4.all fun b => wq a st7 0 4 == wq b st7 0 4) = true := by
  rfl

/-- ALL 42 shapes of size 5, all 1764 ordered pairs. -/
example :
    (shapes5.all fun a => shapes5.all fun b => wq a st7 0 5 == wq b st7 0 5) = true := by
  rfl

/-- Size 4, quantified over 3 stores and 4 endpoint pairs as well:
    14 x 14 x 3 x 4 = 2352 ordered checks, all kernel-checked. -/
example :
    ([(0, 4), (1, 3), (2, 2), (0, 8)].all fun lr =>
      [st7, stT, stF].all fun st =>
        shapes4.all fun a => shapes4.all fun b =>
          wq a st lr.1 lr.2 == wq b st lr.1 lr.2) = true := by
  rfl

end WQChecked
