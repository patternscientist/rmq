import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL differential against the F2 "S" verdict.

The audited anti-vacuity used sizes 3/4/5 and two CONSTANT-shape stores whose
every reply was a `some` word of a single fixed length.  Small n and uniform
stores are exactly the degenerate regime.  Here:

  * sizes 15/16 and 31/32, i.e. straddling BOTH `machineWordBits` regime
    boundaries (bpCode.length = 30/32/62/64, Nat.log2 = 4/5/5/6);
  * four structurally extreme shapes at each size (left spine, right spine,
    balanced, zig-zag) -- maximally different bpCode at equal size;
  * three stores: variable WORD LENGTH by address, partial (`none` on some
    addresses), and all-none -- these exercise the `match super?,delta?,word?`
    fallback branch and every chunk-fold trip count;
  * three segment bases and 40 positions each, comparing the FULL TraceResult
    (value AND event-by-event trace), not just the value.

If any shape-of-equal-size dependence existed anywhere in the L3 leaf, one of
these cells would differ.
-/

namespace DPXF2B

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

def zig : Nat -> CartesianShape
  | 0 => E
  | 1 => N E E
  | k + 2 => N (N E (zig k)) E

def bal : Nat -> Nat -> CartesianShape
  | 0, _ => E
  | _, 0 => E
  | f + 1, k + 1 => N (bal f (k / 2)) (bal f (k - k / 2))

def shapesOfSize (k : Nat) : List CartesianShape :=
  [spineL k, spineR k, zig k, bal 64 k]

/-! ## stores designed to be hostile -/

def storeVarLen : WordRAM.ReadStore where
  readWord? seg i :=
    some ((List.range (3 + (seg * 5 + i * 7) % 9)).map
      (fun j => decide ((seg * 13 + i * 11 + j * 3) % 7 < 3)))

def storePartial : WordRAM.ReadStore where
  readWord? seg i :=
    if (seg + i) % 4 == 0 then none
    else some ((List.range (2 + (seg * 3 + i) % 11)).map
      (fun j => decide ((seg + i * 5 + j * 2) % 3 == 0)))

def storeNone : WordRAM.ReadStore where
  readWord? _ _ := none

def stores : List WordRAM.ReadStore := [storeVarLen, storePartial, storeNone]

def leaf (st : WordRAM.ReadStore) (s : CartesianShape) (base pos : Nat) :
    WordRAM.TraceResult Nat :=
  concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore s st base pos

def addrStream (t : WordRAM.TraceResult Nat) : List (Nat × Nat) :=
  t.trace.filterMap fun ev =>
    match ev with
    | .readWord seg i _ => some (seg, i)
    | _ => none

/-- full observable of one leaf run: value + entire address stream + trace length -/
def obs (st : WordRAM.ReadStore) (s : CartesianShape) (base pos : Nat) :
    Nat × Nat × List (Nat × Nat) :=
  let t := leaf st s base pos
  (t.value, t.trace.length, addrStream t)

def bases : List Nat := [17, 0, 3]
def poss : List Nat := List.range 40

/-- for one size: the number of DISTINCT observables across the four extreme
shapes, summed over every (store, base, pos) cell.  4 shapes agreeing on every
cell gives exactly one distinct observable per cell. -/
def distinctAcrossShapes (k : Nat) : Nat × Nat :=
  let shapes := shapesOfSize k
  let cells :=
    stores.flatMap fun st =>
      bases.flatMap fun b =>
        poss.map fun p => (shapes.map fun s => obs st s b p).eraseDups.length
  (cells.length, cells.foldl max 0)

-- sanity: the four shapes really have the intended size and DISTINCT bpCode
#eval (shapesOfSize 15).map CartesianShape.size
#eval (shapesOfSize 16).map CartesianShape.size
#eval (shapesOfSize 31).map CartesianShape.size
#eval (shapesOfSize 32).map CartesianShape.size
#eval ((shapesOfSize 15).map CartesianShape.bpCode).eraseDups.length
#eval ((shapesOfSize 16).map CartesianShape.bpCode).eraseDups.length
#eval ((shapesOfSize 31).map CartesianShape.bpCode).eraseDups.length
#eval ((shapesOfSize 32).map CartesianShape.bpCode).eraseDups.length

-- geometry regime really does change at 15->16 and 31->32
#eval (shapesOfSize 15).map (fun s =>
  ((builtRelativeSplitBPCloseRankData s).wordSize,
   (builtRelativeSplitBPCloseRankData s).blocksPerSuper,
   SuccinctClose.bpFringeChunkBits s.bpCode.length))
#eval (shapesOfSize 16).map (fun s =>
  ((builtRelativeSplitBPCloseRankData s).wordSize,
   (builtRelativeSplitBPCloseRankData s).blocksPerSuper,
   SuccinctClose.bpFringeChunkBits s.bpCode.length))
#eval (shapesOfSize 31).map (fun s =>
  ((builtRelativeSplitBPCloseRankData s).wordSize,
   (builtRelativeSplitBPCloseRankData s).blocksPerSuper,
   SuccinctClose.bpFringeChunkBits s.bpCode.length))
#eval (shapesOfSize 32).map (fun s =>
  ((builtRelativeSplitBPCloseRankData s).wordSize,
   (builtRelativeSplitBPCloseRankData s).blocksPerSuper,
   SuccinctClose.bpFringeChunkBits s.bpCode.length))

-- THE ATTACK: (#cells, max distinct observables per cell).  max must be 1.
#eval distinctAcrossShapes 15
#eval distinctAcrossShapes 16
#eval distinctAcrossShapes 31
#eval distinctAcrossShapes 32

-- ANTI-VACUITY at the SAME regime boundaries: different size must differ
#eval (obs storeVarLen (spineL 15) 17 20) == (obs storeVarLen (spineL 16) 17 20)
#eval (obs storeVarLen (spineL 31) 17 40) == (obs storeVarLen (spineL 32) 17 40)
#eval addrStream (leaf storeVarLen (spineL 15) 17 20)
#eval addrStream (leaf storeVarLen (spineL 16) 17 20)
#eval addrStream (leaf storeVarLen (spineL 31) 17 40)
#eval addrStream (leaf storeVarLen (spineL 32) 17 40)

-- and the partial / none stores really do drive the fallback branch
#eval (leaf storeNone (spineL 16) 17 20).value
#eval (leaf storeNone (spineL 16) 17 20).trace.length
#eval (leaf storePartial (spineL 16) 17 20).value
#eval (leaf storeVarLen (spineL 16) 17 20).value

end DPXF2B
