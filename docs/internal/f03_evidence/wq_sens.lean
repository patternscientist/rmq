import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! What exactly is the whole query sensitive to?  Separate ADDRESSES (the
    ordered read footprint) from REPLIES (the returned words) and from the
    VALUE.  This calibrates what cross-shape agreement is evidence OF. -/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal

namespace WQSens

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def leftSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (leftSpine n) .empty
def rightSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node .empty (rightSpine n)

def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w
def addrStore (salt width : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range width).map fun b => ((seg * 131 + idx * 17 + salt) >>> b) % 2 == 1)

def wq (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s st l r
def fp (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore s st l r

#eval show IO Unit from do
  let n := 5
  let s := leftSpine n
  let sts : List (String × WordRAM.ReadStore) :=
    [ ("flatF", flatStore (List.replicate 16 false))
    , ("flatT", flatStore (List.replicate 16 true))
    , ("addr7", addrStore 7 24)
    , ("addr9", addrStore 9 24) ]
  IO.println "-- store sensitivity at fixed shape/endpoints (n=5, l=0, r=5) --"
  for (nm, st) in sts do
    let r := wq s st 0 n
    IO.println s!"  store={nm} footprint={fp s st 0 n} value={r.value} traceLen={r.trace.length}"
  IO.println "-- footprint equal across stores? --"
  let base := fp s (flatStore (List.replicate 16 false)) 0 n
  for (nm, st) in sts do
    IO.println s!"  {nm}: footprintSameAsFlatF={fp s st 0 n == base}"
  IO.println "-- endpoint sensitivity at fixed shape/store --"
  for (l, r) in [(0,5), (1,3), (2,2), (0,10)] do
    let x := wq s (addrStore 7 24) l r
    IO.println s!"  l={l} r={r} footprint={fp s (addrStore 7 24) l r} value={x.value}"
  IO.println "-- REAL store: does the value track the shape (correctness liveness)? --"
  for m in [4, 5, 6] do
    let a := leftSpine m
    let b := rightSpine m
    let ra := wq a (BPNavigation.concreteBPCloseNavigationGlobalReadStore a) 0 (m - 1)
    let rb := wq b (BPNavigation.concreteBPCloseNavigationGlobalReadStore b) 0 (m - 1)
    IO.println s!"  n={m} leftSpine(realA).value={ra.value} rightSpine(realB).value={rb.value} same={ra.value == rb.value}"
    let rc := wq b (BPNavigation.concreteBPCloseNavigationGlobalReadStore a) 0 (m - 1)
    IO.println s!"       MISMATCHED: rightSpine queried against realStore(leftSpine).value={rc.value} equalsA={rc.value == ra.value} traceEqA={rc.trace == ra.trace}"

end WQSens
