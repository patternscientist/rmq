import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! Incremental-logging timing probe: where does the cost blow up? -/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace AdvS6P

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def logFile : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advS_f6_probe_log.txt"

def logLine (s : String) : IO Unit := do
  let h <- IO.FS.Handle.mk logFile IO.FS.Mode.append
  h.putStrLn s
  h.flush

def L1raw (bits : List Bool) (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData bits false)
    |>.bpChunkedSelectTraceResultWithStore
      concreteBPNativeSelectCloseTraceSegmentLayout
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeSelectChunkTraceSegment store
      (SuccinctClose.bpFringeChunkBits bits.length) idx

def noiseStore (salt : Nat) : WordRAM.ReadStore where
  readWord? segment index :=
    some ((List.range 16).map fun k =>
      (salt + segment * 7919 + index * 104729 + k * 1299709) % 3 == 0)

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

def spine : List Bool -> CartesianShape
  | [] => CartesianShape.empty
  | true :: bs => CartesianShape.node CartesianShape.empty (spine bs)
  | false :: bs => CartesianShape.node (spine bs) CartesianShape.empty

#eval show IO Unit from do
  IO.FS.writeFile logFile "probe start\n"
  for n in [16, 32, 40, 48, 56, 63, 65] do
    let s := spine (List.replicate n true)
    let t0 <- IO.monoMsNow
    let bits := s.bpCode
    let occ := GenericSelect.occurrenceCount bits false
    let t1 <- IO.monoMsNow
    logLine s!"n={n} len={bits.length} occ={occ} occTime={t1-t0}ms"
    let t2 <- IO.monoMsNow
    let k := key (L1raw bits (noiseStore 11) 3)
    let t3 <- IO.monoMsNow
    logLine s!"  L1raw idx=3 time={t3-t2}ms keyLen={k.length}"
  logLine "probe done"

end AdvS6P
