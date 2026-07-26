import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! Focused adversarial attack: hostile/partial stores, REAL base 17, probe arity,
    long-word replies. Regimes the defender did not execute. -/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctRank

namespace AdvF3

def F1 (shape : CartesianShape) (store : WordRAM.ReadStore) (base pos : Nat) :
    WordRAM.TraceResult Nat :=
  RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
    shape store base pos

def obs (r : WordRAM.TraceResult Nat) : Nat × List WordRAM.TraceEvent := (r.value, r.trace)

def reads (r : WordRAM.TraceResult Nat) : List (Nat × Nat) :=
  r.trace.filterMap fun e =>
    match e with
    | WordRAM.TraceEvent.readWord s i _ => some (s, i)
    | _ => none

def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node CartesianShape.empty (rightSpine n)

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (leftSpine n) CartesianShape.empty

def zigzag : Nat -> Bool -> CartesianShape
  | 0, _ => CartesianShape.empty
  | Nat.succ n, true => CartesianShape.node (zigzag n false) CartesianShape.empty
  | Nat.succ n, false => CartesianShape.node CartesianShape.empty (zigzag n true)

def comb : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | 1 => CartesianShape.node CartesianShape.empty CartesianShape.empty
  | (n + 2) =>
      CartesianShape.node (CartesianShape.node CartesianShape.empty CartesianShape.empty) (comb n)

def family (n : Nat) : List (String × CartesianShape) :=
  [("rspine", rightSpine n), ("lspine", leftSpine n),
   ("zigL", zigzag n true), ("zigR", zigzag n false), ("comb", comb n)]

def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w

def hashStore : WordRAM.ReadStore where
  readWord? := fun seg i =>
    some ((List.range 16).map (fun k => (seg * 7 + i * 13 + k * 5) % 3 == 0))

def noneStore : WordRAM.ReadStore where
  readWord? := fun _ _ => none

def dropSeg (s : Nat) : WordRAM.ReadStore where
  readWord? := fun seg i => if seg = s then none else hashStore.readWord? seg i

def wildStore : WordRAM.ReadStore where
  readWord? := fun seg i =>
    if (seg + i) % 5 = 0 then none
    else some ((List.range ((seg * 3 + i * 7) % 40 + 1)).map fun k => (k * i + seg) % 2 == 0)

def hugeStore : WordRAM.ReadStore where
  readWord? := fun _ _ => some (List.replicate 1000 true)

def stores : List (String × WordRAM.ReadStore) :=
  [("hash", hashStore), ("flatEmpty", flatStore []), ("none", noneStore),
   ("dropWord19", dropSeg 19), ("dropSuper17", dropSeg 17), ("dropBlock18", dropSeg 18),
   ("dropChunk21", dropSeg 21), ("wild", wildStore), ("huge1000", hugeStore)]

def posesFor (n : Nat) : List Nat := [0, 1, 7, n, 2 * n - 1, 2 * n, 2 * n + 1, 100000]

def bases : List Nat := [0, 17]

def sigAll (n : Nat) (s : CartesianShape) : List (Nat × List WordRAM.TraceEvent) :=
  stores.flatMap fun st =>
    bases.flatMap fun b => (posesFor n).map fun p => obs (F1 s st.2 b p)

-- ATTACK 1: cross-shape under hostile/partial stores, real base, wide pos
#eval show IO Unit from do
  for n in [7, 9, 16, 17, 33, 64, 100] do
    let fam := family n
    let sizesOk := fam.all (fun p => p.2.size == n)
    let base := sigAll n (fam.headD ("x", CartesianShape.empty)).2
    let mut differ : List String := []
    for (nm, s) in fam do
      if sigAll n s != base then differ := differ ++ [nm]
    IO.println s!"ATTACK1 n={n} sizesOk={sizesOk} cases={base.length} SHAPESDIFFERING={differ}"

-- ATTACK 3: arity + segments actually touched, at real base 17
#eval show IO Unit from do
  let mut maxReads := 0
  let mut worst := ""
  let mut segsSeen : List Nat := []
  for n in [1, 2, 7, 16, 33, 100] do
    for (snm, st) in stores do
      for (_, s) in family n do
        for p in posesFor n do
          let rs := reads (F1 s st 17 p)
          if rs.length > maxReads then
            maxReads := rs.length; worst := s!"n={n} store={snm} pos={p}"
          for (sg, _) in rs do
            if !segsSeen.contains sg then segsSeen := segsSeen ++ [sg]
  IO.println s!"ATTACK3 maxProbes={maxReads} at({worst}) segmentsTouched={segsSeen} (base+3=20 must be absent)"

-- ATTACK 4: anti-vacuity of this sweep
#eval show IO Unit from do
  let s := rightSpine 33
  IO.println s!"AV sig(n=33) == sig(n=32)? {sigAll 33 s == sigAll 33 (rightSpine 32)}"
  IO.println s!"AV reads hash n=33 pos=20 = {reads (F1 s hashStore 17 20)}"
  IO.println s!"AV reads huge n=33 pos=20 = {reads (F1 s hugeStore 17 20)}"
  IO.println s!"AV reads wild n=33 pos=20 = {reads (F1 s wildStore 17 20)}"
  IO.println s!"AV vals hash={(F1 s hashStore 17 20).value} huge={(F1 s hugeStore 17 20).value} none={(F1 s noneStore 17 20).value}"

end AdvF3
