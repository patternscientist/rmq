import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL test of the *P* leg of the F2 verdict ("the tables/bitWords reach
the controller only as COUNTED probe replies").

The audited evidence cited only `..._matchesReadStore`, which proves every
EMITTED event reports the store's word.  That is the wrong direction: it does
not rule out a read the leaf performs WITHOUT emitting an event (an uncounted
probe / oracle).

Test: perturb the store at every address OUTSIDE the emitted footprint of a
run.  If any read is uncounted, the perturbed run must diverge.
-/

namespace DPXF2C

open RMQ
open RMQ.SuccinctFinal
open RMQ.Cartesian

def E : CartesianShape := .empty
def N (l r : CartesianShape) : CartesianShape := .node l r

def spineL : Nat -> CartesianShape
  | 0 => E
  | k + 1 => N (spineL k) E

def spineR : Nat -> CartesianShape
  | 0 => E
  | k + 1 => N E (spineR k)

def bal : Nat -> Nat -> CartesianShape
  | 0, _ => E
  | _, 0 => E
  | f + 1, k + 1 => N (bal f (k / 2)) (bal f (k - k / 2))

def baseStore : WordRAM.ReadStore where
  readWord? seg i :=
    some ((List.range (3 + (seg * 5 + i * 7) % 9)).map
      (fun j => decide ((seg * 13 + i * 11 + j * 3) % 7 < 3)))

def leaf (st : WordRAM.ReadStore) (s : CartesianShape) (base pos : Nat) :
    WordRAM.TraceResult Nat :=
  concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore s st base pos

def addrStream (t : WordRAM.TraceResult Nat) : List (Nat × Nat) :=
  t.trace.filterMap fun ev =>
    match ev with
    | .readWord seg i _ => some (seg, i)
    | _ => none

/-- store that agrees with `baseStore` exactly on `foot` and returns a loud,
different word everywhere else. -/
def perturbed (foot : List (Nat × Nat)) : WordRAM.ReadStore where
  readWord? seg i :=
    if foot.contains (seg, i) then baseStore.readWord? seg i
    else some (List.replicate 12 true)

/-- store that also DROPS every off-footprint address. -/
def perturbedNone (foot : List (Nat × Nat)) : WordRAM.ReadStore where
  readWord? seg i :=
    if foot.contains (seg, i) then baseStore.readWord? seg i else none

def cellOK (s : CartesianShape) (base pos : Nat) : Bool :=
  let t := leaf baseStore s base pos
  let foot := addrStream t
  let t1 := leaf (perturbed foot) s base pos
  let t2 := leaf (perturbedNone foot) s base pos
  (t.value == t1.value) && (addrStream t == addrStream t1) &&
    (t.trace.length == t1.trace.length) &&
  (t.value == t2.value) && (addrStream t == addrStream t2) &&
    (t.trace.length == t2.trace.length)

def shapes : List CartesianShape :=
  [spineL 3, spineR 5, bal 64 16, spineL 16, spineR 31, bal 64 32, spineL 64]

def cells : List Bool :=
  shapes.flatMap fun s =>
    [17, 0, 3].flatMap fun b =>
      (List.range 40).map fun p => cellOK s b p

-- how many (shape, base, pos) cells, and how many SURVIVE off-footprint
-- perturbation.  If these are equal, no read is uncounted in any tested cell.
#eval cells.length
#eval (cells.filter (fun b => b)).length
#eval cells.all (fun b => b)

-- anti-vacuity: perturbing ON the footprint DOES change the answer
def onFootPerturb (s : CartesianShape) (base pos : Nat) : Bool :=
  let t := leaf baseStore s base pos
  let bad : WordRAM.ReadStore := { readWord? := fun _ _ => some (List.replicate 12 true) }
  t.value == (leaf bad s base pos).value
#eval (shapes.map (fun s => onFootPerturb s 17 20))

-- the footprints really are proper subsets of the addresses touched by the store
#eval addrStream (leaf baseStore (spineL 16) 17 20)
#eval addrStream (leaf baseStore (bal 64 32) 17 40)
#eval addrStream (leaf baseStore (spineL 64) 17 100)

end DPXF2C
