import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
EG-CP-F01 small-size / threshold SCAN (exploratory, `#eval` only).
Nat-only mirrors of the route's gating predicates, scanned to locate exact
flip points.  Every mirror is bridged to the real route definition in the
companion theorem file.
-/

namespace KsmScan

open RMQ
open RMQ.SuccinctClose

/-! ## Nat mirrors -/

def base (n : Nat) : Nat := Nat.log2 n + 1
def blockSizeRaw (n : Nat) : Nat := 2 * base n
def bpsRaw (n : Nat) : Nat := base n
def blockCountRaw (n : Nat) : Nat := n / base n
def superCountRaw (n : Nat) : Nat := blockCountRaw n / bpsRaw n + 1
def superWidth (n : Nat) : Nat := Nat.log2 (2 * n) + 1
def relWidthRaw (n : Nat) : Nat := 2 * (Nat.log2 (base n) + 1) + 3

def activeNat (n : Nat) : Bool :=
  decide (blockCountRaw n * blockSizeRaw n <= 2 * n) &&
  decide (2 * (bpsRaw n * blockSizeRaw n) < 2 ^ relWidthRaw n) &&
  decide (blockSizeRaw n < 2 ^ relWidthRaw n) &&
  decide (superCountRaw n * superWidth n <= 16 * (n / (Nat.log2 n + 1))) &&
  decide (3 * (blockCountRaw n * relWidthRaw n) <=
    64 * ((n / (Nat.log2 n + 1)) * (Nat.log2 (Nat.log2 n + 1) + 1))) &&
  decide (relWidthRaw n <= Nat.log2 (2 * n) + 1)

def readyNat (n : Nat) : Bool :=
  activeNat n && decide (base n * base n <= n / base n)

/-! ## Real route predicates on real shapes -/

open RMQ.Cartesian

def balanced : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | n + 1 =>
      CartesianShape.node (balanced ((n + 1) / 2)) (balanced (n - (n + 1) / 2))
decreasing_by all_goals omega

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | n + 1 => CartesianShape.node (leftSpine n) CartesianShape.empty

/-! ## Scans -/

def firstTrue (f : Nat -> Bool) (lo hi : Nat) : Option Nat :=
  (List.range' lo (hi - lo)).find? f

def flips (f : Nat -> Bool) (lo hi : Nat) : List (Nat × Bool) :=
  let ns := List.range' lo (hi - lo)
  ns.filterMap (fun n => if n = lo then some (n, f n)
    else if f n = f (n - 1) then none else some (n, f n))

#eval s!"activeNat first true in [0,4096): {firstTrue activeNat 0 4096}"
#eval s!"activeNat flips in [0,8192): {flips activeNat 0 8192}"
#eval s!"readyNat first true in [0,8192): {firstTrue readyNat 0 8192}"
#eval s!"readyNat flips in [0,70000): {flips readyNat 0 70000}"
#eval s!"readyNat false-set in [1000,2000): {((List.range' 1000 1000).filter (fun n => ! readyNat n)).take 40}"
#eval s!"readyNat false count in [1000,70000): {((List.range' 1000 69000).filter (fun n => ! readyNat n)).length}"
#eval s!"readyNat max false n in [1000,70000): {((List.range' 1000 69000).filter (fun n => ! readyNat n)).getLast?}"

-- small-size table
#eval (List.range 20).map (fun n => (n, base n, blockCountRaw n, superCountRaw n,
  activeNat n, readyNat n))

-- confirm mirror against real route on real shapes at the interesting sizes
def probes : List Nat := [0,1,2,3,4,5,9,10,11,255,256,511,512,513,999,1000,1001,1023,1024]

#eval probes.map (fun n =>
  let s := balanced n
  (n, s.size,
   decide (canonicalBPRelativeMinMaxArgSummaryTableActive s) == activeNat n,
   decide (concreteBPRelativeRmmInteriorReady s) == readyNat n))

#eval probes.map (fun n =>
  let s := leftSpine n
  (n, s.size,
   decide (canonicalBPRelativeMinMaxArgSummaryTableActive s) == activeNat n,
   decide (concreteBPRelativeRmmInteriorReady s) == readyNat n))

/-! ## superIsLong crossover: superLongSpan m vs m -/

open RMQ.GenericSelect in
#eval ((List.range 26).map (fun k => 2 ^ k)).filter
  (fun m => decide (superLongSpan m < m))

open RMQ.GenericSelect in
#eval s!"least m with superLongSpan m < m in [0,20000): {firstTrue (fun m => decide (superLongSpan m < m)) 0 20000}"

open RMQ.GenericSelect in
#eval s!"superLongSpan-lt flips in [0,300000): {flips (fun m => decide (superLongSpan m < m)) 0 300000}"

/-! ## the gated geometry below/above the Active threshold -/

#eval probes.map (fun n =>
  let s := balanced n
  (n, canonicalBPRelativeSummaryBlockSize s,
      canonicalBPRelativeSummaryBlockCount s,
      canonicalBPRelativeSummarySuperCount s,
      canonicalBPRelativeSummaryBlocksPerSuper s))

end KsmScan
