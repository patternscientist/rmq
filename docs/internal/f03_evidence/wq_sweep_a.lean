import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
F03 CROSS-SHAPE WHOLE-QUERY SWEEP, TIER A (inactive summary regime, n <= 129).

Hypothesis under test (H): the whole-query GLOBAL WORD TRACE and VALUE are
functions of `(n, left, right, probe replies)` only.  Under a FIXED shape-free
store the replies are pinned, so H predicts: for every two shapes of equal size,
every store, and every endpoint pair, the FULL trace and the value coincide.

A single disagreeing (shapeA, shapeB, store, l, r) is a CHECKED_OBSTRUCTION
witness.  Comparison is against a per-(n,store,l,r) base shape; agreement with
the base is transitive, so k shapes give k-1 comparisons covering all pairs.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctClose

namespace WQSweepA

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

/-! ## Shape families, all of exact size n -/

def leftSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (leftSpine n) .empty

def rightSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node .empty (rightSpine n)

partial def balanced : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (balanced (n / 2)) (balanced (n - n / 2))

/-- Alternating comb: left child, right child, left child, ... -/
def zigzag : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => if n % 2 == 0 then .node (zigzag n) .empty else .node .empty (zigzag n)

/-- `cliff K`: all opens packed, then all closes, then perfect alternation.
    bpCode = true^(K+1) false^(K+1) (true false)^M. -/
def cliff (n k : Nat) : CartesianShape :=
  if n == 0 then .empty
  else .node (leftSpine (min k (n - 1))) (rightSpine (n - 1 - min k (n - 1)))

/-- Mirror of `cliff`. -/
def cliffR (n k : Nat) : CartesianShape :=
  if n == 0 then .empty
  else .node (rightSpine (min k (n - 1))) (leftSpine (n - 1 - min k (n - 1)))

partial def pseudo (seed : Nat) : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n =>
      let k := (seed * 1103515245 + 12345) % (n + 1)
      .node (pseudo (seed + 7) k) (pseudo (seed + 13) (n - k))

/-- Balanced but skewed 1:3. -/
partial def skew : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (skew (n / 4)) (skew (n - n / 4))

def families (n : Nat) : List (String × CartesianShape) :=
  [ ("leftSpine",  leftSpine n)
  , ("rightSpine", rightSpine n)
  , ("balanced",   balanced n)
  , ("zigzag",     zigzag n)
  , ("skew",       skew n)
  , ("cliff/4",    cliff n (n / 4))
  , ("cliff/2",    cliff n (n / 2))
  , ("cliff3/4",   cliff n (3 * n / 4))
  , ("cliffR/2",   cliffR n (n / 2))
  , ("pseudo1",    pseudo 1 n)
  , ("pseudo7",    pseudo 7 n)
  , ("pseudo29",   pseudo 29 n)
  , ("pseudo101",  pseudo 101 n)
  ]

/-! ## Shape-free stores.  None of these mentions any shape. -/

def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w

def addrStore (salt width : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range width).map fun b => ((seg * 131 + idx * 17 + salt) >>> b) % 2 == 1)

def emptyStore : WordRAM.ReadStore where
  readWord? := fun _ _ => none

/-- Partial store: refuses even segments. -/
def partialStore : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    if seg % 2 == 0 then none
    else some ((List.range 20).map fun b => ((seg * 7 + idx * 13) >>> b) % 2 == 1)

def stores : List (String × WordRAM.ReadStore) :=
  [ ("flat0",   flatStore (List.replicate 16 false))
  , ("flat1",   flatStore (List.replicate 16 true))
  , ("alt16",   flatStore ((List.range 16).map fun b => b % 2 == 0))
  , ("narrow4", flatStore [true, false, false, true])
  , ("addr0w16",    addrStore 0 16)
  , ("addr7w24",    addrStore 7 24)
  , ("addr12345w32", addrStore 12345 32)
  , ("none",    emptyStore)
  , ("partial", partialStore)
  ]

def endpoints (n : Nat) : List (Nat × Nat) :=
  [ (0, n), (0, n - 1), (0, 0), (1, 1), (n, n), (1, n - 1)
  , (n / 2, n / 2), (n / 3, 2 * n / 3), (n - 1, n)
  , (0, 2 * n), (n, 0), (2 * n, 2 * n) ]

def wq (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s st l r

structure Tally where
  cmps : Nat := 0
  traceDiff : Nat := 0
  valDiff : Nat := 0
  genBugs : Nat := 0

def sweep (sizes : List Nat) (sts : List (String × WordRAM.ReadStore))
    (label : String) : IO Tally := do
  let mut t : Tally := {}
  for n in sizes do
    let fams := families n
    -- generator sanity: every family must have size exactly n
    for (nm, s) in fams do
      if s.size != n then
        t := { t with genBugs := t.genBugs + 1 }
        IO.println s!"  GENBUG {label} n={n} {nm} size={s.size}"
    let good := fams.filter (fun p => p.2.size == n)
    let active : Bool := decide (canonicalBPRelativeMinMaxArgSummaryTableActive (leftSpine n))
    match good with
    | [] => pure ()
    | (bn, b) :: rest =>
      for (stn, st) in sts do
        for (l, r) in endpoints n do
          let br := wq b st l r
          let bt := br.trace
          let bv := br.value
          for (nm, s) in rest do
            t := { t with cmps := t.cmps + 1 }
            let x := wq s st l r
            if x.trace != bt then
              t := { t with traceDiff := t.traceDiff + 1 }
              IO.println s!"  *** TRACE DIVERGENCE n={n} active={active} store={stn} l={l} r={r} base={bn} other={nm}"
              IO.println s!"      base.bp={b.bpCode}"
              IO.println s!"      othr.bp={s.bpCode}"
              IO.println s!"      lens={bt.length} vs {x.trace.length}"
              let z := (bt.zip x.trace).findIdx? (fun p => p.1 != p.2)
              IO.println s!"      firstDiffIdx={z} base={repr (z.bind (bt[·]?))} othr={repr (z.bind (x.trace[·]?))}"
            if x.value != bv then
              t := { t with valDiff := t.valDiff + 1 }
              IO.println s!"  *** VALUE DIVERGENCE n={n} active={active} store={stn} l={l} r={r} base={bn}({bv}) other={nm}({x.value})"
              IO.println s!"      base.bp={b.bpCode}"
              IO.println s!"      othr.bp={s.bpCode}"
    IO.println s!"  [{label}] done n={n} active={active} shapes={good.length} runningCmps={t.cmps} traceDiff={t.traceDiff} valDiff={t.valDiff}"
  return t

#eval show IO Unit from do
  IO.println "=== TIER A1: every size 1..20, all 13 families, all 9 stores, all 12 endpoint pairs ==="
  let a1 <- sweep (List.range 20 |>.map (· + 1)) stores "A1"
  IO.println s!"A1 TOTAL comparisons={a1.cmps} traceDisagreements={a1.traceDiff} valueDisagreements={a1.valDiff} genBugs={a1.genBugs}"

#eval show IO Unit from do
  IO.println "=== TIER A2: word/power boundaries 24..129, all 13 families, all 9 stores, all 12 endpoints ==="
  let a2 <- sweep [24, 31, 32, 33, 47, 48, 63, 64, 65, 96, 127, 128, 129] stores "A2"
  IO.println s!"A2 TOTAL comparisons={a2.cmps} traceDisagreements={a2.traceDiff} valueDisagreements={a2.valDiff} genBugs={a2.genBugs}"

end WQSweepA
