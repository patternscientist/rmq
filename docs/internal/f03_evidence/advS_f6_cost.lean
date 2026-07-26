import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
Final probe.
(a) Attribute the evaluation cost of the leaf: is it the guard
    `occurrenceCount`, or the construction of the content-bearing tables?
(b) Huge idx values.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.GenericSelect

namespace AdvS6G

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def logFile : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advS_f6_cost_log.txt"

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

def smallStore (salt : Nat) : WordRAM.ReadStore where
  readWord? segment index :=
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

def timed (label : String) (f : Unit -> Nat) : IO Unit := do
  let t0 <- IO.monoMsNow
  let v := f ()
  let t1 <- IO.monoMsNow
  logLine s!"    {label} = {v}  [{t1 - t0}ms]"

#eval show IO Unit from do
  IO.FS.writeFile logFile "cost probe\n"
  for n in [63, 100] do
    let bits := (spine (pat 1 n)).bpCode
    logLine s!"  n={n} len={bits.length}"
    timed "occurrenceCount bits false (the ONLY consumed content channel)"
      (fun _ => occurrenceCount bits false)
    timed "(longSuperFlagBits bits false).length"
      (fun _ => (longSuperFlagBits bits false).length)
    timed "(sparseExceptionEffectiveFlagBits bits false).length"
      (fun _ => (sparseExceptionEffectiveFlagBits bits false).length)
    timed "(superEntries bits false).length (content-bearing, NEVER consumed)"
      (fun _ => (superEntries bits false).length)
    timed "sparseExceptionSelectData bits false |>.wordSize (forces the whole record)"
      (fun _ => (sparseExceptionSelectData bits false).wordSize)

#eval show IO Unit from do
  logLine "  huge idx"
  let store := smallStore 7
  for n in [63, 65] do
    let fam := [ ("rightComb", spine (List.replicate n true))
               , ("leftComb", spine (List.replicate n false))
               , ("rand1", spine (pat 1 n)) ]
    for idx in [n, n + 1, 2 * n, 1000, 1000000, 1000000000] do
      let ks := (fam.map fun p =>
        key (concreteBPNativeSelectCloseGlobalWordTraceResultWithStore p.2 store idx)).eraseDups
      logLine s!"    n={n} idx={idx} distinctOutcomes={ks.length} value={(ks.head!).take 12}"

end AdvS6G
