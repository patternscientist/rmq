import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! Clean cost attribution: FRESH leaf call (no hoisting), per regime, per n. -/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.GenericSelect

namespace AdvS6I

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def logFile : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advS_f6_cost3_log.txt"

def logLine (s : String) : IO Unit := do
  let h <- IO.FS.Handle.mk logFile IO.FS.Mode.append
  h.putStrLn s
  h.flush

def spine : List Bool -> CartesianShape
  | [] => CartesianShape.empty
  | true :: bs => CartesianShape.node CartesianShape.empty (spine bs)
  | false :: bs => CartesianShape.node (spine bs) CartesianShape.empty

def pat (seed n : Nat) : List Bool :=
  (List.range n).map fun i => (seed * 977 + i * 1103 + i * i * 65537) % 7 < 3

def regimeStore (salt : Nat) (superMark localMark : Bool) :
    WordRAM.ReadStore where
  readWord? segment index :=
    if segment == 3 then
      some (if superMark then [true, false, false, false] else [false, false, false, false])
    else if segment == 7 then
      some (if localMark then [true, false, false, false] else [false, false, false, false])
    else
      let v := (salt + segment * 5 + index * 3) % 16
      some ((List.range 4).map fun k => (v / 2 ^ k) % 2 == 1)

def evCount (r : WordRAM.TraceResult (Option Nat)) : Nat := r.trace.length

/-- Fresh call through the PUBLIC leaf, nothing hoisted. -/
def freshLeaf (s : CartesianShape) (store : WordRAM.ReadStore) (idx : Nat) : Nat :=
  evCount (concreteBPNativeSelectCloseGlobalWordTraceResultWithStore s store idx)

#eval show IO Unit from do
  IO.FS.writeFile logFile "cost3\n"
  for n in [16, 32, 63, 100, 128] do
    let s := spine (pat 1 n)
    for (lbl, st) in [("LONG", regimeStore 7 true false),
                      ("SPARSE", regimeStore 7 false true),
                      ("DENSE", regimeStore 7 false false)] do
      let t0 <- IO.monoMsNow
      let c := freshLeaf s st 5
      let t1 <- IO.monoMsNow
      logLine s!"  n={n} regime={lbl} traceEvents={c} freshLeafTime={t1-t0}ms"

end AdvS6I
