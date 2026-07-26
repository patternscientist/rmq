import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
F03 CROSS-SHAPE WHOLE-QUERY SWEEP, TIER B: ACROSS THE SUMMARY-TABLE THRESHOLD.

`canonicalBPRelativeMinMaxArgSummaryTableActive` is FALSE for every size 0..511
and TRUE from 512 (measured, single flip, see wq_thresh.lean).  Tier A covers the
inactive arm densely.  Tier B is the treatment: n = 512 and n = 640 (ACTIVE),
against n = 384 and n = 511 as inactive controls, i.e. both sides of the only
regime boundary reachable at feasible sizes.

Progress is written with explicit flushes to a log file because #eval buffers
stdout.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctClose

namespace WQSweepB

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
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/wq_sweep_b_log.txt"

#eval show IO Unit from do
  let h <- IO.FS.Handle.mk logPath IO.FS.Mode.write
  let say (s : String) : IO Unit := do h.putStrLn s; h.flush; IO.println s
  say "=== TIER B: whole query across the summary-table threshold ==="
  let sts : List (String × WordRAM.ReadStore) :=
    [ ("addr7w24", addrStore 7 24), ("flat1", flatStore (List.replicate 16 true)) ]
  let mut cmps := 0
  let mut traceDiff := 0
  let mut valDiff := 0
  for n in [384, 511, 512, 640] do
    let fams : List (String × CartesianShape) :=
      [ ("leftSpine", leftSpine n), ("rightSpine", rightSpine n)
      , ("balanced", balanced n), ("cliff/2", cliff n (n / 2))
      , ("pseudo1", pseudo 1 n) ]
    for (nm, s) in fams do
      if s.size != n then say s!"GENBUG n={n} {nm} size={s.size}"
    let (bn, b) := fams.head!
    let active : Bool := decide (canonicalBPRelativeMinMaxArgSummaryTableActive b)
    say s!"--- n={n} bpLen={b.bpCode.length} summaryTableActive={active}"
    for (stn, st) in sts do
      for (l, r) in [(0, n - 1), (1, n / 2), (n / 2, n - 1), (0, n)] do
        let t0 <- IO.monoMsNow
        let br := wq b st l r
        let bt := br.trace
        let bv := br.value
        let t1 <- IO.monoMsNow
        say s!"  base {bn} store={stn} l={l} r={r}: traceLen={bt.length} value={bv} ms={t1 - t0}"
        for (nm, s) in fams.tail! do
          cmps := cmps + 1
          let x := wq s st l r
          let ok := x.trace == bt && x.value == bv
          if ok then
            say s!"    ok {nm}: identical trace ({x.trace.length} events) and value"
          else
            if x.trace != bt then traceDiff := traceDiff + 1
            if x.value != bv then valDiff := valDiff + 1
            say s!"    *** DIVERGENCE n={n} active={active} store={stn} l={l} r={r} base={bn} other={nm}"
            say s!"        lens={bt.length} vs {x.trace.length} values={bv} vs {x.value}"
            let z := (bt.zip x.trace).findIdx? (fun p => p.1 != p.2)
            say s!"        firstDiffIdx={z}"
            say s!"        base@={repr (z.bind (bt[·]?))}"
            say s!"        othr@={repr (z.bind (x.trace[·]?))}"
            say s!"        base.bp={b.bpCode}"
            say s!"        othr.bp={s.bpCode}"
  say s!"TIER B TOTAL comparisons={cmps} traceDisagreements={traceDiff} valueDisagreements={valDiff}"
  h.flush

end WQSweepB
