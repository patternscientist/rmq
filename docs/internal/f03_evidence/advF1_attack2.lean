import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL attack on the F1 = S verdict, regimes OUTSIDE the defender's sweep:
large n, PARTIAL/failing stores, pos far past 2n, the REAL segment base (17, not 6),
and end-to-end controller reachability.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctRank

namespace AdvF1

#print RMQ.SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase

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

-- structurally different shapes of a given size
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

def balancedF : Nat -> Nat -> CartesianShape
  | 0, _ => CartesianShape.empty
  | _, 0 => CartesianShape.empty
  | Nat.succ f, Nat.succ m =>
      CartesianShape.node (balancedF f (m / 2)) (balancedF f (m - m / 2))

def balanced (n : Nat) : CartesianShape := balancedF n n

def family (n : Nat) : List (String × CartesianShape) :=
  [("rspine", rightSpine n), ("lspine", leftSpine n), ("bal", balanced n),
   ("zigL", zigzag n true), ("zigR", zigzag n false), ("comb", comb n)]

-- HOSTILE stores. base+k segments for the REAL base 17 are 17,18,19,21.
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

def bigTrueStore : WordRAM.ReadStore where
  readWord? := fun _ _ => some (List.replicate 64 true)

def stores : List (String × WordRAM.ReadStore) :=
  [("hash", hashStore), ("flat8", flatStore [true,false,true,false,true,false,true,false]),
   ("flatEmpty", flatStore []), ("none", noneStore),
   ("dropWord19", dropSeg 19), ("dropSuper17", dropSeg 17), ("dropChunk21", dropSeg 21),
   ("dropWord8", dropSeg 8), ("wild", wildStore), ("bigTrue", bigTrueStore)]

def posesFor (n : Nat) : List Nat :=
  [0, 1, 2, 3, 7, 13, n, 2 * n - 1, 2 * n, 2 * n + 1, 2 * n + 37, 100000, 1000000]

def bases : List Nat := [0, 6, 5, 7, 17, 12345]

def sigAll (n : Nat) (s : CartesianShape) : List (Nat × List WordRAM.TraceEvent) :=
  stores.flatMap fun st =>
    bases.flatMap fun b =>
      (posesFor n).map fun p => obs (F1 s st.2 b p)

-- ATTACK 1: large-n, hostile-store, wide-pos, multi-base cross-shape comparison
#eval show IO Unit from do
  for n in [7, 8, 9, 16, 17, 33, 64, 100, 200, 513] do
    let fam := family n
    let sizesOk := fam.all (fun p => p.2.size == n)
    let bpLens := fam.map (fun p => p.2.bpCode.length)
    let base := sigAll n (fam.headD ("x", CartesianShape.empty)).2
    let mut differ : List String := []
    for (nm, s) in fam do
      if sigAll n s != base then differ := differ ++ [nm]
    IO.println s!"ATTACK1 n={n} sizesAllEqualN={sizesOk} bpLens={bpLens} cases={base.length} shapesDiffering={differ}"

-- ATTACK 2: probe ADDRESS lists across shapes, per hostile store, at REAL base 17
#eval show IO Unit from do
  let mut leaks := 0
  for n in [16, 100, 513] do
    for (snm, st) in stores do
      for p in [0, 7, n, 2 * n, 2 * n + 9] do
        let fam := family n
        let b := reads (F1 (fam.headD ("x", CartesianShape.empty)).2 st 17 p)
        let mut differ : List String := []
        for (nm, s) in fam do
          if reads (F1 s st 17 p) != b then differ := differ ++ [nm]
        if differ != [] then
          leaks := leaks + 1
          IO.println s!"ATTACK2 LEAK n={n} store={snm} pos={p} differing={differ}"
  IO.println s!"ATTACK2 totalLeaks={leaks}"

-- ATTACK 3: probe arity / segment claims, at REAL base 17
#eval show IO Unit from do
  let mut maxReads := 0
  let mut segsSeen : List Nat := []
  let mut worst := ""
  for n in [1, 2, 3, 7, 16, 33, 100, 200, 513] do
    for (snm, st) in stores do
      for (_, s) in family n do
        for p in posesFor n do
          let rs := reads (F1 s st 17 p)
          if rs.length > maxReads then
            maxReads := rs.length
            worst := s!"n={n} store={snm} pos={p}"
          for (sg, _) in rs do
            if !segsSeen.contains sg then segsSeen := segsSeen ++ [sg]
  IO.println s!"ATTACK3 maxProbes={maxReads} at {worst} segmentsTouched={segsSeen}"

-- ATTACK 4: anti-vacuity of MY OWN sweep
#eval show IO Unit from do
  let s16 := rightSpine 16
  let s17 := rightSpine 17
  IO.println s!"ATTACK4 sig(n=16) == sig(n=17) ? {(sigAll 16 s16) == (sigAll 16 s17)}"
  IO.println s!"ATTACK4 reads hash n=16 pos=9 base17={reads (F1 s16 hashStore 17 9)}"
  IO.println s!"ATTACK4 reads wild n=16 pos=9 base17={reads (F1 s16 wildStore 17 9)}"
  IO.println s!"ATTACK4 reads dropWord19 n=16 pos=9={reads (F1 s16 (dropSeg 19) 17 9)}"
  IO.println s!"ATTACK4 vals hash={(F1 s16 hashStore 17 9).value} wild={(F1 s16 wildStore 17 9).value} none={(F1 s16 noneStore 17 9).value}"
  IO.println s!"ATTACK4 n=513 reads={reads (F1 (rightSpine 513) hashStore 17 700)}"

end AdvF1
