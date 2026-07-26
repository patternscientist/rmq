import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! Cross-shape whole-query sweep at the largest sizes that complete:
    n = 160..512, narrow grid, flushing log so partial results survive. -/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctClose

namespace WQBig

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
def cliff (n k : Nat) : CartesianShape :=
  if n == 0 then .empty
  else .node (leftSpine (min k (n - 1))) (rightSpine (n - 1 - min k (n - 1)))
def deep (n : Nat) : CartesianShape :=
  if n < 2 then .empty else .node (rightSpine 1) (leftSpine (n - 2))
partial def pseudo (seed : Nat) : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n =>
      let k := (seed * 1103515245 + 12345) % (n + 1)
      .node (pseudo (seed + 7) k) (pseudo (seed + 13) (n - k))

def addrStore (salt width : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range width).map fun b => ((seg * 131 + idx * 17 + salt) >>> b) % 2 == 1)
def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w

def wq (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s st l r

def logPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/wq_sweep_big_log.txt"

#eval show IO Unit from do
  let h <- IO.FS.Handle.mk logPath IO.FS.Mode.write
  let say (s : String) : IO Unit := do h.putStrLn s; h.flush; IO.println s
  say "=== LARGE-n cross-shape whole-query sweep ==="
  let sts : List (String × WordRAM.ReadStore) :=
    [ ("addr7w24", addrStore 7 24)
    , ("flat1", flatStore (List.replicate 16 true))
    , ("addr0w16", addrStore 0 16) ]
  let mut gCmp := 0
  let mut gTd := 0
  let mut gVd := 0
  for n in [160, 192, 224, 256, 320, 384, 448, 512] do
    let fams : List (String × CartesianShape) :=
      [ ("leftSpine", leftSpine n), ("rightSpine", rightSpine n)
      , ("balanced", balanced n), ("cliff/2", cliff n (n / 2))
      , ("deep", deep n), ("pseudo1", pseudo 1 n), ("pseudo29", pseudo 29 n) ]
    let good := fams.filter (fun p => p.2.size == n)
    for (nm, s) in fams.filter (fun p => p.2.size != n) do
      say s!"  GENBUG n={n} {nm} size={s.size} (excluded)"
    let (bn, b) := good.head!
    let active : Bool := decide (canonicalBPRelativeMinMaxArgSummaryTableActive b)
    let mut cmp := 0
    let mut td := 0
    let mut vd := 0
    let mut outcomes : List (List WordRAM.TraceEvent × Option Nat) := []
    for (stn, st) in sts do
      for (l, r) in [(0, n - 1), (1, n / 2), (n / 2, n - 1), (0, n), (0, 2 * n)] do
        let t0 <- IO.monoMsNow
        let br := wq b st l r
        let key := (br.trace, br.value)
        if !(outcomes.contains key) then outcomes := key :: outcomes
        for (nm, s) in good.tail! do
          cmp := cmp + 1
          let x := wq s st l r
          if x.trace != br.trace then
            td := td + 1
            say s!"  *** TRACE DIVERGENCE n={n} store={stn} l={l} r={r} base={bn} other={nm}"
            say s!"      lens={br.trace.length} vs {x.trace.length}"
            let z := (br.trace.zip x.trace).findIdx? (fun p => p.1 != p.2)
            say s!"      firstDiffIdx={z} base@={repr (z.bind (br.trace[·]?))} othr@={repr (z.bind (x.trace[·]?))}"
          if x.value != br.value then
            vd := vd + 1
            say s!"  *** VALUE DIVERGENCE n={n} store={stn} l={l} r={r} base={bn}({br.value}) other={nm}({x.value})"
        let t1 <- IO.monoMsNow
        say s!"    n={n} store={stn} l={l} r={r}: base traceLen={br.trace.length} value={br.value} cellMs={t1 - t0} runningCmp={cmp} td={td} vd={vd}"
    gCmp := gCmp + cmp; gTd := gTd + td; gVd := gVd + vd
    say s!"  == n={n} summaryTableActive={active} shapes={good.length} distinctOutcomes={outcomes.length} comparisons={cmp} traceDiff={td} valDiff={vd}"
  say s!"LARGE-n TOTAL comparisons={gCmp} traceDisagreements={gTd} valueDisagreements={gVd}"
  h.flush

end WQBig
