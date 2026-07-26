import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL attack on the F1 = S verdict.
Regimes deliberately OUTSIDE the defender's executed sweep (n<=6, 3 benign
total stores, pos<=100, bases {0,6}):
  * large n (multi-superblock, chunk-cap saturation)
  * PARTIAL stores (readWord? = none on selected segments) -> the `_,_,_ => pure 0` branch
  * pos far past 2n (clamping regime) and pos = 0 edge
  * structurally maximally-different shapes of equal size
  * end-to-end controller reachability
-/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctRank

namespace AdvF1

/-- Name-resolution trap check: what does the bare name actually resolve to? -/
#check @concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
#print RMQ.SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase

def F1 (shape : CartesianShape) (store : WordRAM.ReadStore) (base pos : Nat) :
    WordRAM.TraceResult Nat :=
  RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
    shape store base pos

def reads (r : WordRAM.TraceResult Nat) : List (Nat × Nat) :=
  r.trace.filterMap fun e =>
    match e with
    | WordRAM.TraceEvent.readWord s i _ => some (s, i)
    | _ => none

/-! ### structurally maximally different shapes of a GIVEN size -/

def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node CartesianShape.empty (rightSpine n)

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (leftSpine n) CartesianShape.empty

partial def balanced (n : Nat) : CartesianShape :=
  if n = 0 then CartesianShape.empty
  else
    let m := n - 1
    CartesianShape.node (balanced (m / 2)) (balanced (m - m / 2))

/-- zigzag: alternate which side carries the whole remaining mass -/
partial def zigzag (n : Nat) (leftFirst : Bool) : CartesianShape :=
  if n = 0 then CartesianShape.empty
  else if leftFirst then CartesianShape.node (zigzag (n - 1) false) CartesianShape.empty
  else CartesianShape.node CartesianShape.empty (zigzag (n - 1) true)

/-- comb: every other node has a singleton left child -/
partial def comb (n : Nat) : CartesianShape :=
  if n = 0 then CartesianShape.empty
  else if n = 1 then CartesianShape.node CartesianShape.empty CartesianShape.empty
  else CartesianShape.node (CartesianShape.node CartesianShape.empty CartesianShape.empty)
        (comb (n - 2))

def family (n : Nat) : List (String × CartesianShape) :=
  [("rspine", rightSpine n), ("lspine", leftSpine n), ("bal", balanced n),
   ("zigL", zigzag n true), ("zigR", zigzag n false), ("comb", comb n)]

/-! ### HOSTILE stores (the defender only used total, benign ones) -/

def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w

def hashStore : WordRAM.ReadStore where
  readWord? := fun seg i =>
    some ((List.range 16).map (fun k => (seg * 7 + i * 13 + k * 5) % 3 == 0))

/-- total failure -/
def noneStore : WordRAM.ReadStore where
  readWord? := fun _ _ => none

/-- fails ONLY on the packed-word segment base+2 (base=6) -> forces the fallback branch -/
def noWordStore : WordRAM.ReadStore where
  readWord? := fun seg i => if seg = 8 then none else hashStore.readWord? seg i

/-- fails ONLY on the superblock sample segment -/
def noSuperStore : WordRAM.ReadStore where
  readWord? := fun seg i => if seg = 6 then none else hashStore.readWord? seg i

/-- fails ONLY on the fringe chunk table segment base+4 -/
def noChunkStore : WordRAM.ReadStore where
  readWord? := fun seg i => if seg = 10 then none else hashStore.readWord? seg i

/-- address-sensitive: reply length and content vary wildly with index -/
def wildStore : WordRAM.ReadStore where
  readWord? := fun seg i =>
    if (seg + i) % 5 = 0 then none
    else some ((List.range ((seg * 3 + i * 7) % 40 + 1)).map fun k => (k * i + seg) % 2 == 0)

/-- long words, all true -/
def bigTrueStore : WordRAM.ReadStore where
  readWord? := fun _ _ => some (List.replicate 64 true)

def stores : List (String × WordRAM.ReadStore) :=
  [("hash", hashStore), ("flat8", flatStore [true,false,true,false,true,false,true,false]),
   ("flatEmpty", flatStore []), ("none", noneStore), ("noWord", noWordStore),
   ("noSuper", noSuperStore), ("noChunk", noChunkStore), ("wild", wildStore),
   ("bigTrue", bigTrueStore)]

def posesFor (n : Nat) : List Nat :=
  [0, 1, 2, 3, 7, 13, n, 2 * n - 1, 2 * n, 2 * n + 1, 2 * n + 37, 100000, 1000000]

def bases : List Nat := [0, 6, 5, 7, 12345]

/-- full observable signature of F1 for one shape: value AND trace, over all
    bases/positions/stores. Any shape-content leak anywhere shows up here. -/
def sigAll (n : Nat) (s : CartesianShape) : List (WordRAM.TraceResult Nat) :=
  stores.flatMap fun st =>
    bases.flatMap fun b =>
      (posesFor n).map fun p => F1 s st.2 b p

/-- ATTACK 1: large-n, hostile-store, wide-pos cross-shape comparison. -/
#eval show IO Unit from do
  for n in [7, 8, 9, 16, 17, 33, 64, 100, 200, 513] do
    let fam := family n
    let sizesOk := fam.all (fun p => p.2.size == n)
    let base := sigAll n (fam.headD ("x", CartesianShape.empty)).2
    let mut differ : List String := []
    for (nm, s) in fam do
      if sigAll n s != base then differ := differ ++ [nm]
    IO.println s!"ATTACK1 n={n} sizesAllEqualN={sizesOk} cases={base.length} shapesDiffering={differ}"

/-- ATTACK 2: does any hostile store make the PROBE LIST shape-dependent?
    (separate from values: addresses are what F03 cares about) -/
#eval show IO Unit from do
  for n in [16, 100, 513] do
    for (snm, st) in stores do
      let fam := family n
      let b := reads (F1 (fam.headD ("x", CartesianShape.empty)).2 st 6 (n + 3))
      let mut differ : List String := []
      for (nm, s) in fam do
        if reads (F1 s st 6 (n + 3)) != b then differ := differ ++ [nm]
      if differ != [] then
        IO.println s!"ATTACK2 LEAK n={n} store={snm} differing={differ}"
  IO.println "ATTACK2 done (only LEAK lines above would be refutations)"

/-- ATTACK 3: probe arity and segment claims ("<=11 probes", "base+3 never read"). -/
#eval show IO Unit from do
  let mut maxReads := 0
  let mut sawBase3 := false
  let mut segsSeen : List Nat := []
  for n in [1, 2, 3, 7, 16, 33, 100, 200, 513] do
    for (_, st) in stores do
      for (_, s) in family n do
        for p in posesFor n do
          let rs := reads (F1 s st 6 p)
          if rs.length > maxReads then maxReads := rs.length
          for (sg, _) in rs do
            if sg = 9 then sawBase3 := true
            if !segsSeen.contains sg then segsSeen := segsSeen ++ [sg]
  IO.println s!"ATTACK3 maxProbes={maxReads} readsBasePlus3(seg9)={sawBase3} segmentsTouched={segsSeen}"

/-- ATTACK 4 (anti-vacuity of MY sweep): the signature really does move
    with n and with the store, so ATTACK1/2 finding nothing is meaningful. -/
#eval show IO Unit from do
  let s16 := rightSpine 16
  let s17 := rightSpine 17
  IO.println s!"ATTACK4 n16-vs-n17 sameSig={(sigAll 16 s16) == (sigAll 16 s17)}"
  IO.println s!"ATTACK4 hash-vs-wild sameReads={reads (F1 s16 hashStore 6 9) == reads (F1 s16 wildStore 6 9)}"
  IO.println s!"ATTACK4 reads(hash,n=16,pos=9)={reads (F1 s16 hashStore 6 9)}"
  IO.println s!"ATTACK4 reads(wild,n=16,pos=9)={reads (F1 s16 wildStore 6 9)}"
  IO.println s!"ATTACK4 reads(noWord,n=16,pos=9)={reads (F1 s16 noWordStore 6 9)}"
  IO.println s!"ATTACK4 vals hash={(F1 s16 hashStore 6 9).value} wild={(F1 s16 wildStore 6 9).value} none={(F1 s16 noneStore 6 9).value}"

end AdvF1
