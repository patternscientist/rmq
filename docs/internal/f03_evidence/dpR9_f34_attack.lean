import RMQ.Core.SuccinctFinal
import RMQ.Core.SuccinctRMQClassic

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace DpR9

abbrev Sh := Cartesian.CartesianShape

def sup (s : Sh) : Nat := builtRelativeSplitBPCloseRankSuperOverhead s
def blk (s : Sh) : Nat := builtRelativeSplitBPCloseRankBlockOverhead s

/-! ## ATTACK A: a CLOSED PROGRAM in `n : Nat` with no shape in scope at all.
    Stronger than "same size implies same value": the controller can literally
    run this. -/

def wOf (n : Nat) : Nat := SuccinctRank.machineWordBits (2 * n)
def bwOf (n : Nat) : Nat := SuccinctRank.machineWordBits (wOf n * wOf n)

def supOfN (n : Nat) : Nat :=
  (2 * n / wOf n / wOf n + 1) * wOf n + (2 * n / wOf n / wOf n + 1) * wOf n

def blkOfN (n : Nat) : Nat :=
  (2 * n / wOf n + 1) * bwOf n + (2 * n / wOf n + 1) * bwOf n

theorem dpR9_sup_closed (s : Sh) : sup s = supOfN s.size := by
  unfold sup supOfN wOf builtRelativeSplitBPCloseRankSuperOverhead
  rw [SuccinctRank.canonicalSuperRankSampleTables_payload_length,
    canonicalSuperRankEntries_length, canonicalSuperRankEntries_length]
  simp [builtRelativeSplitBPCloseRankWordSize,
    builtRelativeSplitBPCloseRankBlocksPerSuper,
    Cartesian.CartesianShape.bpCode_length]

theorem dpR9_blk_closed (s : Sh) : blk s = blkOfN s.size := by
  unfold blk blkOfN bwOf wOf builtRelativeSplitBPCloseRankBlockOverhead
  rw [SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan_payload_length,
    canonicalBlockRankEntries_length, canonicalBlockRankEntries_length]
  simp [builtRelativeSplitBPCloseRankWordSize,
    builtRelativeSplitBPCloseRankBlocksPerSuper,
    builtRelativeSplitBPCloseRankBlockWidth,
    Cartesian.CartesianShape.bpCode_length]

theorem dpR9_same_size (s t : Sh) (h : s.size = t.size) :
    sup s = sup t /\ blk s = blk t := by
  constructor
  · rw [dpR9_sup_closed, dpR9_sup_closed, h]
  · rw [dpR9_blk_closed, dpR9_blk_closed, h]

/-- Public entry, via the ACTUAL public constant `SuccinctClassic.cartesianShape`
    (the prior report named a namespace that does not exist; this is the real one). -/
theorem dpR9_public_entry (xs : List Int) :
    sup (SuccinctClassic.cartesianShape xs) = supOfN xs.length
    /\ blk (SuccinctClassic.cartesianShape xs) = blkOfN xs.length := by
  constructor
  · rw [dpR9_sup_closed, SuccinctClassic.cartesianShape, Cartesian.shape_size]
  · rw [dpR9_blk_closed, SuccinctClassic.cartesianShape, Cartesian.shape_size]

#print axioms dpR9_sup_closed
#print axioms dpR9_blk_closed
#print axioms dpR9_same_size
#print axioms dpR9_public_entry

/-! ## ATTACK B: EXECUTION in regimes the prior audit never entered.
    Prior audit ran sizes 0..8 only; there `2n/w/w` is ALWAYS 0 (one super
    sample).  Below the super-sample count becomes 2, 3, 9, ... -/

def leftSpine : Nat -> Sh
  | 0 => .empty
  | n + 1 => .node (leftSpine n) .empty

def rightSpine : Nat -> Sh
  | 0 => .empty
  | n + 1 => .node .empty (rightSpine n)

def balanced : Nat -> Sh
  | 0 => .empty
  | n + 1 => .node (balanced (n / 2)) (balanced (n - n / 2))

def combAux : Nat -> Sh
  | 0 => .empty
  | 1 => .node .empty .empty
  | n + 2 => .node (.node .empty .empty) (combAux n)

def lcgStep (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

def randList (seed n : Nat) : List Int :=
  (List.range n).map (fun i =>
    Int.ofNat ((Nat.rec (motive := fun _ => Nat) seed (fun _ x => lcgStep x) (i + 1)) % 100000))

def family (n : Nat) : List Sh :=
  [leftSpine n, rightSpine n, balanced n, combAux n,
   Cartesian.shape (randList 1 n), Cartesian.shape (randList 7 n),
   Cartesian.shape (randList 991 n), Cartesian.shape (randList 424242 n)]

#eval show IO Unit from do
  IO.println "== ATTACK B: n | superSampleCount 2n/w/w+1 | allSizesEqualN | distinct (sup,blk) | #distinct bpCodes | closedFormMatches =="
  for n in [0,1,2,3,4,8,16,31,32,33,63,64,65,100,127,128,129,200,255,256,257,400,512,600] do
    let fam := family n
    let sizesOk := fam.all (fun s => s.size == n)
    let pairs := (fam.map (fun s => (sup s, blk s))).eraseDups
    let codes := (fam.map (fun s => s.bpCode)).eraseDups
    let cnt := 2 * n / wOf n / wOf n + 1
    let okClosed := pairs == [(supOfN n, blkOfN n)]
    IO.println s!"{n} | superCnt={cnt} | sizesOk={sizesOk} | pairs={pairs} | distinctCodes={codes.length} | closedOk={okClosed}"

/-! ## ATTACK C: exhaustive re-run with MY OWN enumerator (independent of
    `Cartesian.shapesOfSize`), sizes 0..10. -/

def shapesUpTo : Nat -> Array (List Sh)
  | 0 => #[[Cartesian.CartesianShape.empty]]
  | n + 1 =>
      let prev := shapesUpTo n
      let cur : List Sh :=
        (List.range (n + 1)).flatMap (fun i =>
          (prev[i]!).flatMap (fun l => (prev[n - i]!).map (fun r =>
            Cartesian.CartesianShape.node l r)))
      prev.push cur

def allOf (n : Nat) : List Sh := (shapesUpTo n)[n]!

#eval show IO Unit from do
  IO.println "== ATTACK C: exhaustive, own enumerator | n | #shapes | #distinctCodes | distinct pairs | matchesClosedForm | agreesWithRepoEnum =="
  for n in List.range 11 do
    let ss := allOf n
    let pairs := (ss.map (fun s => (sup s, blk s))).eraseDups
    let codes := (ss.map (fun s => s.bpCode)).eraseDups
    let repo := Cartesian.shapesOfSize n
    let agree := (ss.length == repo.length) && ss.all (fun s => repo.contains s)
    IO.println s!"{n} | {ss.length} | {codes.length} | {pairs} | {pairs == [(supOfN n, blkOfN n)]} | {agree}"

/-! ## ATTACK D: anti-vacuity at LARGE n.  If the sample CONTENTS were also
    identical across shapes, the constancy would be vacuous. -/

#eval show IO Unit from do
  IO.println "== ATTACK D: at n, do the actual rank SAMPLE ENTRIES differ between leftSpine and rightSpine? =="
  for n in [64,128,256,512] do
    let a := leftSpine n
    let b := rightSpine n
    let w := builtRelativeSplitBPCloseRankWordSize a
    let ea := SuccinctRank.canonicalSuperRankEntries true a.bpCode w w
    let eb := SuccinctRank.canonicalSuperRankEntries true b.bpCode w w
    let ba := SuccinctRank.canonicalBlockRankEntries true a.bpCode w w
    let bb := SuccinctRank.canonicalBlockRankEntries true b.bpCode w w
    IO.println s!"n={n} superEntriesDiffer={ea != eb} blockEntriesDiffer={ba != bb} lens=({ea.length},{eb.length},{ba.length},{bb.length}) supA={sup a} supB={sup b} blkA={blk a} blkB={blk b}"
    IO.println s!"   superA={ea.take 8} superB={eb.take 8}"

/-! ## ATTACK E: public entry executed -- same length n, wildly different Int
    lists (hence different Cartesian shapes). -/

#eval show IO Unit from do
  IO.println "== ATTACK E: public entry | n | distinct (sup,blk) over 6 different xs | #distinct bpCodes =="
  for n in [1,2,5,10,33,64,100,257] do
    let xss : List (List Int) :=
      [ (List.range n).map (fun i => Int.ofNat i)
      , (List.range n).map (fun i => Int.ofNat (n - i))
      , (List.range n).map (fun _ => (0 : Int))
      , (List.range n).map (fun i => if i % 2 == 0 then (0 : Int) else 1)
      , randList 5 n, randList 777 n ]
    let shs := xss.map SuccinctClassic.cartesianShape
    let pairs := (shs.map (fun s => (sup s, blk s))).eraseDups
    let codes := (shs.map (fun s => s.bpCode)).eraseDups
    IO.println s!"{n} | {pairs} | {codes.length} | closedOk={pairs == [(supOfN n, blkOfN n)]}"

end DpR9
