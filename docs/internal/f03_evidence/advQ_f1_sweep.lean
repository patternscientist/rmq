import Lean
import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctRank
namespace AdvQF1S
instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩
def rspine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node CartesianShape.empty (rspine n)
def F1 (shape : CartesianShape) (store : WordRAM.ReadStore) (base pos : Nat) :
    WordRAM.TraceResult Nat :=
  RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
    shape store base pos

def reads (shape : CartesianShape) (store : WordRAM.ReadStore) (base pos : Nat) :
    List (Nat × Nat) :=
  (F1 shape store base pos).trace.filterMap fun e =>
    match e with
    | WordRAM.TraceEvent.readWord s i _ => some (s, i)
    | _ => none

def lspine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (lspine n) CartesianShape.empty

partial def balanced : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (balanced (n / 2)) (balanced (n - n / 2))

partial def zig : Nat -> Bool -> CartesianShape
  | 0, _ => CartesianShape.empty
  | Nat.succ n, b =>
      if b then CartesianShape.node CartesianShape.empty (zig n false)
      else CartesianShape.node (zig n true) CartesianShape.empty

partial def prand : Nat -> Nat -> CartesianShape
  | 0, _ => CartesianShape.empty
  | Nat.succ n, seed =>
      let k := (seed * 1103515 + 12345) % (n + 1)
      CartesianShape.node (prand k (seed * 31 + 7)) (prand (n - k) (seed * 17 + 3))

def families (n : Nat) : List (String × CartesianShape) :=
  [("rspine", rspine n), ("lspine", lspine n), ("balanced", balanced n),
   ("zig", zig n true), ("rand1", prand n 1), ("rand2", prand n 12345),
   ("rand3", prand n 777777)]

def stNone : WordRAM.ReadStore where readWord? := fun _ _ => none

def stFlat (w : List Bool) : WordRAM.ReadStore where readWord? := fun _ _ => some w

-- none exactly on the packed-word segment (base+2 with base=6 => 8)
def stHoleWord : WordRAM.ReadStore where
  readWord? := fun seg _ => if seg == 8 then none else some [true, false, true]

def stHoleSuper : WordRAM.ReadStore where
  readWord? := fun seg _ => if seg == 6 then none else some [true, false, true]

-- ragged widths: returned word length swings wildly with the index
def stRagged : WordRAM.ReadStore where
  readWord? := fun seg i =>
    some ((List.range ((seg * 13 + i * 29) % 71)).map (fun k => (k * 7 + i) % 3 == 0))

def stHash : WordRAM.ReadStore where
  readWord? := fun seg i =>
    some ((List.range 64).map (fun k => (seg * 7 + i * 13 + k * 5) % 3 == 0))

def storeList : List (String × WordRAM.ReadStore) :=
  [("none", stNone), ("flat0", stFlat [true, false, true, false]),
   ("flatEmpty", stFlat []), ("holeWord", stHoleWord), ("holeSuper", stHoleSuper),
   ("ragged", stRagged), ("hash", stHash)]

def posesFor (n : Nat) : List Nat :=
  [0, 1, n - 1, n, n + 1, 2 * n - 1, 2 * n, 2 * n + 1, 4 * n, 1000000]

def basesList : List Nat := [6, 17]

def sigOf (s : CartesianShape) (store : WordRAM.ReadStore) (n : Nat) :
    List (Nat × List WordRAM.TraceEvent) :=
  basesList.flatMap fun b =>
    (posesFor n).map fun p => let r := F1 s store b p; (r.value, r.trace)

-- A: cross-family differential at LARGE n. Any nonzero violation refutes S.
#eval show IO Unit from do
  for n in [7, 16, 31, 64, 100, 127, 256] do
    let fams := families n
    let base := fams.head!
    let mut bad : List String := []
    for (nm, st) in storeList do
      let bsig := sigOf base.2 st n
      for (fnm, s) in fams do
        if s.size != n then bad := bad ++ [s!"SIZEBUG {fnm}={s.size}"]
        if sigOf s st n != bsig then bad := bad ++ [s!"DIFFER store={nm} fam={fnm}"]
    IO.println s!"LARGE-N n={n} bpLen={base.2.bpCode.length} families={fams.length} stores={storeList.length} violations={bad.length} {bad.take 4}"

-- B: probe-count bound at large n
#eval show IO Unit from do
  let mut worst := 0
  let mut worstAt := ""
  for n in [1, 2, 4, 8, 16, 32, 64, 128, 256] do
    for (nm, st) in storeList do
      for p in posesFor n do
        let k := (reads (rspine n) st 6 p).length
        if k > worst then
          worst := k
          worstAt := s!"n={n} store={nm} pos={p}"
  IO.println s!"MAX-PROBES worst={worst} at {worstAt}"

-- C: anti-vacuity
#eval show IO Unit from do
  for n in [8, 64, 256] do
    IO.println s!"ANTIVAC-N n={n} ragged reads={reads (rspine n) stRagged 6 n} value={(F1 (rspine n) stRagged 6 n).value}"
  for (nm, st) in storeList do
    IO.println s!"ANTIVAC-STORE store={nm} reads={reads (rspine 100) st 6 100} value={(F1 (rspine 100) st 6 100).value}"

-- D: geometry knobs at large n
#eval show IO Unit from do
  for n in [7, 63, 100, 255] do
    let d := builtRelativeSplitBPCloseRankData (rspine n)
    IO.println s!"KNOBS n={n} bpLen={(rspine n).bpCode.length} wordSize={d.wordSize} blocksPerSuper={d.blocksPerSuper} c={RMQ.SuccinctClose.bpFringeChunkBits (rspine n).bpCode.length} qp={d.queryPos n} si={d.superIndex n} wi={d.wordIndex n} wo={d.wordOffset n}"

-- E: the shape families really are distinct trees (guard against a vacuous sweep)
#eval show IO Unit from do
  for n in [7, 16, 63, 100] do
    let fams := families n
    IO.println s!"DISTINCT n={n} distinctBpCodes={((fams.map (fun p => p.2.bpCode)).eraseDups).length} of {fams.length}"

end AdvQF1S
