import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
(B)/(C) select-layer length arithmetic, plus large-n whole-query feasibility.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctClose
open RMQ.GenericSelect

namespace WQThresh2

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
  IO.println "== (B)/(C) select-layer length arithmetic =="
  let mut firstLong : Option Nat := none
  let mut firstSparse : Option Nat := none
  for e in List.range 41 do
    let m := 2 ^ e
    let w := wordBits m
    let l := ell m
    let ls := localStride m
    let sls := superLongSpan m
    let canLong := decide (sls < m)
    let canSparse := decide (2 <= ls)
    if canLong && firstLong.isNone then firstLong := some m
    if canSparse && firstSparse.isNone then firstSparse := some m
    if e <= 16 || canLong || canSparse || e % 4 == 0 then
      IO.println s!"m=2^{e}={m} wordBits={w} ell={l} localStride={ls} superStride={superStride m} superLongSpan={sls} canLong={canLong} canSparse={canSparse}"
  IO.println s!"FIRST bp-length m where superIsLong CAN fire: {firstLong}"
  IO.println s!"FIRST bp-length m where localIsSparse CAN fire (scan to 2^40): {firstSparse}"

#eval show IO Unit from do
  IO.println "== large-n whole-query feasibility =="
  let st := addrStore 3
  for n in [512, 1024, 2048, 4096, 8192] do
    let t0 <- IO.monoMsNow
    let a := wq (leftSpine n) st 0 (n - 1)
    let la := a.trace.length
    let t1 <- IO.monoMsNow
    IO.println s!"n={n} bpLen={2*n} ms={t1 - t0} traceLen={la} value={a.value}"

end WQThresh2
