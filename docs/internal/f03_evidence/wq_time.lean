import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

open RMQ RMQ.Cartesian RMQ.SuccinctFinal

namespace WQTime

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def leftSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (leftSpine n) .empty

def addrStore (salt : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 24).map fun b => ((seg * 131 + idx * 17 + salt) >>> b) % 2 == 1)

def wq (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s st l r

#eval show IO Unit from do
  let st := addrStore 3
  for n in [64, 128, 256, 384, 512, 640, 768, 1024] do
    let t0 <- IO.monoMsNow
    let a := wq (leftSpine n) st 0 (n - 1)
    let la := a.trace.length
    let t1 <- IO.monoMsNow
    IO.println s!"n={n} ms={t1 - t0} traceLen={la} value={a.value}"

end WQTime
