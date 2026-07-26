import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! Which regime pays the content-construction cost? -/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.GenericSelect

namespace AdvS6H

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def logFile : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advS_f6_cost2_log.txt"

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

def wordStr : Option (List Bool) -> String
  | none => "-"
  | some w => String.mk (w.map fun b => if b then '1' else '0')

def evKey : WordRAM.TraceEvent -> String
  | WordRAM.TraceEvent.readWord s i w? => s!"R({s},{i})->{wordStr w?}"
  | WordRAM.TraceEvent.wordRank t l r => s!"WR({t},{l},{r})"
  | WordRAM.TraceEvent.wordSelect t o r => s!"WS({t},{o},{r})"
  | WordRAM.TraceEvent.syntheticCostOnlyPrimitive => "SYN"

def key (r : WordRAM.TraceResult (Option Nat)) : String :=
  s!"{repr r.value}|" ++ String.intercalate ";" (r.trace.map evKey)

def timeQ (label : String) (s : CartesianShape) (store : WordRAM.ReadStore)
    (idx : Nat) : IO Unit := do
  let t0 <- IO.monoMsNow
  let k := key (concreteBPNativeSelectCloseGlobalWordTraceResultWithStore s store idx)
  let t1 <- IO.monoMsNow
  logLine s!"    {label}: [{t1-t0}ms] {k.take 90}"

#eval show IO Unit from do
  IO.FS.writeFile logFile "cost2\n"
  for n in [63, 100] do
    let s := spine (pat 1 n)
    logLine s!"  n={n}"
    timeQ "LONG  " s (regimeStore 7 true false) 5
    timeQ "SPARSE" s (regimeStore 7 false true) 5
    timeQ "DENSE " s (regimeStore 7 false false) 5
    -- forcing the two content-derived rank towers directly
    let t0 <- IO.monoMsNow
    let a := (sparseExceptionSelectData s.bpCode false).longFlagRankData.wordSize
    let t1 <- IO.monoMsNow
    let b := (sparseExceptionSelectData s.bpCode false).sparseDirectory.rankData.wordSize
    let t2 <- IO.monoMsNow
    logLine s!"    longFlagRankData.wordSize={a} [{t1-t0}ms]  sparseDirectory.rankData.wordSize={b} [{t2-t1}ms]"

end AdvS6H
