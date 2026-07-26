import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
Timing probe: is `L1raw` evaluable at the nondegenerate sizes
(superSlotCount >= 2, i.e. n >= 63)?
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace AdvS6T

def L1raw (bits : List Bool) (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData bits false)
    |>.bpChunkedSelectTraceResultWithStore
      concreteBPNativeSelectCloseTraceSegmentLayout
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeSelectChunkTraceSegment store
      (SuccinctClose.bpFringeChunkBits bits.length) idx

/-- Definitional bridge: `L1raw` really is the leaf. -/
theorem L1raw_eq (shape : CartesianShape) (store : WordRAM.ReadStore)
    (idx : Nat) :
    L1raw shape.bpCode store idx =
      concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        shape store idx := rfl

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

/-- Right comb: node empty (node empty (... )). bpCode = (10)^n reversed-ish. -/
def rightComb : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ k => CartesianShape.node CartesianShape.empty (rightComb k)

def leftComb : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ k => CartesianShape.node (leftComb k) CartesianShape.empty

def timeIt (label : String) (act : IO Unit) : IO Unit := do
  let t0 <- IO.monoMsNow
  act
  let t1 <- IO.monoMsNow
  IO.println s!"  [{label}] {t1 - t0} ms"

#eval show IO Unit from do
  for n in [8, 16, 32] do
    timeIt s!"rightComb n={n}" do
      let k := key (L1raw (rightComb n).bpCode (noiseStore 11) 3)
      IO.println s!"n={n} len={(rightComb n).bpCode.length} key={k.length} chars"

end AdvS6T
