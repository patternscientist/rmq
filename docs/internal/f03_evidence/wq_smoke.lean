import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! Smoke: is the WHOLE-QUERY store-parametric evaluator feasible at moderate n? -/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace WQSmoke

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

def addrStore (salt : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 24).map fun b => ((seg * 131 + idx * 17 + salt) >>> b) % 2 == 1)

def wq (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s st l r

#eval show IO Unit from do
  let st := addrStore 3
  for n in [8, 16, 32, 64] do
    let t0 <- IO.monoMsNow
    let a := wq (leftSpine n) st 0 (n - 1)
    let b := wq (rightSpine n) st 0 (n - 1)
    let c := wq (balanced n) st 0 (n - 1)
    let t1 <- IO.monoMsNow
    IO.println s!"n={n} ms={t1 - t0} traceLens=({a.trace.length},{b.trace.length},{c.trace.length}) vals=({a.value},{b.value},{c.value}) sameLR={a.trace == b.trace} sameLB={a.trace == c.trace}"

end WQSmoke
