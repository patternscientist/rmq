import RMQ.Core.SuccinctFinal
import RMQ.Core.SuccinctRMQClassic

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace AdvF34

abbrev Sh := Cartesian.CartesianShape

def sup (s : Sh) : Nat := builtRelativeSplitBPCloseRankSuperOverhead s
def blk (s : Sh) : Nat := builtRelativeSplitBPCloseRankBlockOverhead s

/-- MY OWN exhaustive enumerator: `res[k]` = every shape of size `k`. -/
def shapesUpTo : Nat -> Array (List Sh)
  | 0 => #[[Cartesian.CartesianShape.empty]]
  | n + 1 =>
      let prev := shapesUpTo n
      let cur : List Sh :=
        (List.range (n + 1)).flatMap (fun i =>
          let ls := prev[i]!
          let rs := prev[n - i]!
          ls.flatMap (fun l => rs.map (fun r => Cartesian.CartesianShape.node l r)))
      prev.push cur

def allOf (n : Nat) : List Sh := (shapesUpTo n)[n]!

/-- n-only predicted formula, computed from `n` with NO shape in scope. -/
def predSup (n : Nat) : Nat :=
  let w := SuccinctRank.machineWordBits (2 * n)
  (2 * n / w / w + 1) * w + (2 * n / w / w + 1) * w

def predBlk (n : Nat) : Nat :=
  let w := SuccinctRank.machineWordBits (2 * n)
  let bw := SuccinctRank.machineWordBits (w * w)
  (2 * n / w + 1) * bw + (2 * n / w + 1) * bw

/-! ## 1. Exhaustive sweep, sizes 0..10, my own enumerator -/

def exhaustRow (n : Nat) : Nat × Nat × Nat × List (Nat × Nat) × Bool × Bool :=
  let ss := allOf n
  let pairs := (ss.map (fun s => (sup s, blk s))).eraseDups
  let codes := (ss.map (fun s => s.bpCode)).eraseDups
  let sizesOk := ss.all (fun s => s.size == n)
  let predOk := pairs == [(predSup n, predBlk n)]
  (n, ss.length, codes.length, pairs, sizesOk, predOk)

#eval do
  IO.println "== EXHAUSTIVE (my own enumerator): n, #shapes, #distinct bpCodes, distinct (sup,blk) pairs, allSizesOk, matchesNOnlyFormula =="
  for n in List.range 11 do
    IO.println (toString (exhaustRow n))

/-! ## 2. Cross-check my enumerator against the repo's `Cartesian.shapesOfSize` -/

#eval do
  IO.println "== ENUMERATOR CROSS-CHECK: n, myCount, repoCount, sameSet =="
  for n in List.range 9 do
    let mine := allOf n
    let repo := Cartesian.shapesOfSize n
    let same := (mine.all (fun s => repo.contains s)) && (repo.all (fun s => mine.contains s))
    IO.println s!"{n} {mine.length} {repo.length} {same}"

/-! ## 3. LARGE-n structural extremes (exhaustive enumeration cannot reach here).
    Left spine, right spine, balanced, comb, and pseudo-random Cartesian shapes
    of the SAME size, compared pairwise. -/

def leftSpine : Nat -> Sh
  | 0 => .empty
  | n + 1 => .node (leftSpine n) .empty

def rightSpine : Nat -> Sh
  | 0 => .empty
  | n + 1 => .node .empty (rightSpine n)

def balanced : Nat -> Sh
  | 0 => .empty
  | n + 1 => .node (balanced (n / 2)) (balanced (n - n / 2))

/-- alternating comb: left child a leaf, right child recursive -/
def comb : Nat -> Sh
  | 0 => .empty
  | 1 => .node .empty .empty
  | n + 2 => .node (.node .empty .empty) (comb n)

def lcg (seed : Nat) : Nat := (seed * 1103515245 + 12345) % 2147483648

def randList (seed n : Nat) : List Int :=
  (List.range n).map (fun i =>
    Int.ofNat ((Nat.rec (motive := fun _ => Nat) seed (fun _ s => lcg s) (i + 1)) % 1000))

def randShape (seed n : Nat) : Sh := Cartesian.shape (randList seed n)

def familyOf (n : Nat) : List Sh :=
  [leftSpine n, rightSpine n, balanced n, comb n,
   randShape 1 n, randShape 7 n, randShape 99 n, randShape 12345 n]

def bigRow (n : Nat) : Nat × Bool × List (Nat × Nat) × Nat × Bool :=
  let fam := familyOf n
  let sizesOk := fam.all (fun s => s.size == n)
  let pairs := (fam.map (fun s => (sup s, blk s))).eraseDups
  let codes := (fam.map (fun s => s.bpCode)).eraseDups
  let predOk := pairs == [(predSup n, predBlk n)]
  (n, sizesOk, pairs, codes.length, predOk)

#eval do
  IO.println "== LARGE-n EXTREMES: n, allSameSize, distinct (sup,blk) pairs, #distinct bpCodes in family, matchesNOnlyFormula =="
  for n in [0,1,2,3,5,8,13,17,31,32,33,63,64,65,100,127,128,129,150,200,255,256,257,300] do
    IO.println (toString (bigRow n))

/-! ## 4. Public-entry version: same n, wildly different Int lists -/

#eval do
  IO.println "== PUBLIC ENTRY (Cartesian.shape xs): n, distinct pairs over 6 different xs of that length, #distinct bpCodes =="
  for n in [1,2,3,4,5,10,20,50,100,200] do
    let xss : List (List Int) :=
      [ (List.range n).map (fun i => Int.ofNat i)
      , (List.range n).map (fun i => Int.ofNat (n - i))
      , (List.range n).map (fun _ => (0 : Int))
      , (List.range n).map (fun i => if i % 2 == 0 then (0 : Int) else 1)
      , randList 5 n
      , randList 777 n ]
    let shs : List Sh := xss.map Cartesian.shape
    let pairs := (shs.map (fun s => (sup s, blk s))).eraseDups
    let codes := (shs.map (fun (s : Sh) => s.bpCode)).eraseDups
    IO.println s!"{n} {pairs} {codes.length}"

/-! ## 5. My own checked theorem (written independently), plus axiom audit. -/

theorem adv_sup_closed (s : Sh) : sup s = predSup s.size := by
  unfold sup predSup builtRelativeSplitBPCloseRankSuperOverhead
  rw [SuccinctRank.canonicalSuperRankSampleTables_payload_length,
    canonicalSuperRankEntries_length, canonicalSuperRankEntries_length]
  simp [builtRelativeSplitBPCloseRankWordSize,
    builtRelativeSplitBPCloseRankBlocksPerSuper,
    Cartesian.CartesianShape.bpCode_length]

theorem adv_blk_closed (s : Sh) : blk s = predBlk s.size := by
  unfold blk predBlk builtRelativeSplitBPCloseRankBlockOverhead
  rw [SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan_payload_length,
    canonicalBlockRankEntries_length, canonicalBlockRankEntries_length]
  simp [builtRelativeSplitBPCloseRankWordSize,
    builtRelativeSplitBPCloseRankBlocksPerSuper,
    builtRelativeSplitBPCloseRankBlockWidth,
    Cartesian.CartesianShape.bpCode_length]

theorem adv_same_size_same_value (s t : Sh) (h : s.size = t.size) :
    sup s = sup t /\ blk s = blk t := by
  constructor
  · rw [adv_sup_closed, adv_sup_closed, h]
  · rw [adv_blk_closed, adv_blk_closed, h]

theorem adv_public_entry_is_function_of_n (xs ys : List Int)
    (h : xs.length = ys.length) :
    sup (SuccinctClassic.cartesianShape xs) = sup (SuccinctClassic.cartesianShape ys) /\
      blk (SuccinctClassic.cartesianShape xs) = blk (SuccinctClassic.cartesianShape ys) := by
  apply adv_same_size_same_value
  simp [SuccinctClassic.cartesianShape, Cartesian.shape_size, h]

/-- Fully explicit: both overheads are literally a function of `n` alone at the
    public entry, with the shape eliminated from the statement entirely. -/
theorem adv_public_entry_closed_form (xs : List Int) :
    sup (SuccinctClassic.cartesianShape xs) = predSup xs.length /\
      blk (SuccinctClassic.cartesianShape xs) = predBlk xs.length := by
  constructor
  · rw [adv_sup_closed]
    simp [SuccinctClassic.cartesianShape, Cartesian.shape_size]
  · rw [adv_blk_closed]
    simp [SuccinctClassic.cartesianShape, Cartesian.shape_size]

#print axioms adv_sup_closed
#print axioms adv_blk_closed
#print axioms adv_same_size_same_value
#print axioms adv_public_entry_is_function_of_n
#print axioms adv_public_entry_closed_form

end AdvF34
