import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
F03 CROSS-SHAPE WHOLE-QUERY SWEEP (flushing log), with an HONEST DENOMINATOR.

Two numbers are reported per size, not one:

  comparisons  -- how many (shapeA, shapeB, store, l, r) checks were made;
  cells        -- how many DISTINCT (trace, value) outcomes the (store, l, r)
                  grid actually produces at that size.

`cells` is the honest measure of how much the grid tests.  A grid of 108
(store, endpoint) combinations that all collapse to one outcome is one test
repeated 108 times, not 108 tests.  Reporting only `comparisons` inflates the
evidence; both are printed.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctClose

namespace WQSweepA2

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def leftSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (leftSpine n) .empty
def rightSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node .empty (rightSpine n)
partial def balanced : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (balanced (n / 2)) (balanced (n - n / 2))
def zigzag : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => if n % 2 == 0 then .node (zigzag n) .empty else .node .empty (zigzag n)
partial def skew : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (skew (n / 4)) (skew (n - n / 4))
def cliff (n k : Nat) : CartesianShape :=
  if n == 0 then .empty
  else .node (leftSpine (min k (n - 1))) (rightSpine (n - 1 - min k (n - 1)))
def cliffR (n k : Nat) : CartesianShape :=
  if n == 0 then .empty
  else .node (rightSpine (min k (n - 1))) (leftSpine (n - 1 - min k (n - 1)))
/-- span-maximising family (see wq_longfront.lean) -/
def deep (n : Nat) : CartesianShape :=
  if n == 0 then .empty else .node (rightSpine 1) (leftSpine (n - 2))
partial def pseudo (seed : Nat) : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n =>
      let k := (seed * 1103515245 + 12345) % (n + 1)
      .node (pseudo (seed + 7) k) (pseudo (seed + 13) (n - k))

def families (n : Nat) : List (String × CartesianShape) :=
  [ ("leftSpine", leftSpine n), ("rightSpine", rightSpine n), ("balanced", balanced n)
  , ("zigzag", zigzag n), ("skew", skew n)
  , ("cliff/4", cliff n (n / 4)), ("cliff/2", cliff n (n / 2))
  , ("cliff3/4", cliff n (3 * n / 4)), ("cliffR/2", cliffR n (n / 2))
  , ("deep", deep n)
  , ("pseudo1", pseudo 1 n), ("pseudo7", pseudo 7 n)
  , ("pseudo29", pseudo 29 n), ("pseudo101", pseudo 101 n) ]

def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w
def addrStore (salt width : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range width).map fun b => ((seg * 131 + idx * 17 + salt) >>> b) % 2 == 1)
def emptyStore : WordRAM.ReadStore where
  readWord? := fun _ _ => none
def partialStore : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    if seg % 2 == 0 then none
    else some ((List.range 20).map fun b => ((seg * 7 + idx * 13) >>> b) % 2 == 1)

def stores : List (String × WordRAM.ReadStore) :=
  [ ("flat0", flatStore (List.replicate 16 false))
  , ("flat1", flatStore (List.replicate 16 true))
  , ("alt16", flatStore ((List.range 16).map fun b => b % 2 == 0))
  , ("narrow4", flatStore [true, false, false, true])
  , ("addr0w16", addrStore 0 16)
  , ("addr7w24", addrStore 7 24)
  , ("addr12345w32", addrStore 12345 32)
  , ("none", emptyStore)
  , ("partial", partialStore) ]

def endpoints (n : Nat) : List (Nat × Nat) :=
  [ (0, n), (0, n - 1), (0, 0), (1, 1), (n, n), (1, n - 1)
  , (n / 2, n / 2), (n / 3, 2 * n / 3), (n - 1, n)
  , (0, 2 * n), (n, 0), (2 * n, 2 * n) ]

def wq (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s st l r

def logPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/wq_sweep_a2_log.txt"

#eval show IO Unit from do
  let h <- IO.FS.Handle.mk logPath IO.FS.Mode.write
  let say (s : String) : IO Unit := do h.putStrLn s; h.flush; IO.println s
  say "=== CROSS-SHAPE WHOLE-QUERY SWEEP (14 families x 9 stores x 12 endpoint pairs) ==="
  let mut gCmp := 0
  let mut gTrace := 0
  let mut gVal := 0
  let mut gCells := 0
  let mut gGrid := 0
  for n in [1,2,3,4,5,6,7,8,9,10,12,14,16,20,24,31,32,33,48,63,64,65,96,127,128,129] do
    let fams := (families n).filter (fun p => p.2.size == n)
    let bad := (families n).filter (fun p => p.2.size != n)
    for (nm, s) in bad do say s!"  GENBUG n={n} {nm} size={s.size} (excluded)"
    let (bn, b) := fams.head!
    let mut outcomes : List (List WordRAM.TraceEvent × Option Nat) := []
    let mut cmp := 0
    let mut td := 0
    let mut vd := 0
    let mut grid := 0
    for (stn, st) in stores do
      for (l, r) in endpoints n do
        grid := grid + 1
        let br := wq b st l r
        let key := (br.trace, br.value)
        if !(outcomes.contains key) then outcomes := key :: outcomes
        for (nm, s) in fams.tail! do
          cmp := cmp + 1
          let x := wq s st l r
          if x.trace != br.trace then
            td := td + 1
            say s!"  *** TRACE DIVERGENCE n={n} store={stn} l={l} r={r} base={bn} other={nm}"
            say s!"      lens={br.trace.length} vs {x.trace.length}"
            let z := (br.trace.zip x.trace).findIdx? (fun p => p.1 != p.2)
            say s!"      firstDiffIdx={z} base@={repr (z.bind (br.trace[·]?))} othr@={repr (z.bind (x.trace[·]?))}"
            say s!"      base.bp={b.bpCode}"
            say s!"      othr.bp={s.bpCode}"
          if x.value != br.value then
            vd := vd + 1
            say s!"  *** VALUE DIVERGENCE n={n} store={stn} l={l} r={r} base={bn}({br.value}) other={nm}({x.value})"
            say s!"      base.bp={b.bpCode}"
            say s!"      othr.bp={s.bpCode}"
    gCmp := gCmp + cmp; gTrace := gTrace + td; gVal := gVal + vd
    gCells := gCells + outcomes.length; gGrid := gGrid + grid
    say s!"  n={n} shapes={fams.length} gridCells={grid} DISTINCToutcomes={outcomes.length} comparisons={cmp} traceDiff={td} valDiff={vd}"
  say s!"TOTAL comparisons={gCmp} traceDisagreements={gTrace} valueDisagreements={gVal}"
  say s!"TOTAL grid cells={gGrid} of which DISTINCT outcomes={gCells}  (honest denominator)"
  h.flush

end WQSweepA2
