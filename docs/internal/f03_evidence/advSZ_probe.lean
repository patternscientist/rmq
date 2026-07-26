import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL attack on the SIZE-ONLY verdict.
Stage 0: feasibility / timing probe. Enumerate same-size shapes and evaluate
the claimed-S quantities plus the two payload-LENGTH frontier constants
F3/F4 (builtRelativeSplitBPCloseRank{Block,Super}Overhead), which are the
prime suspects: they are `payload.length` of tables built from bpCode CONTENT.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open RMQ.SuccinctSpace

namespace AdvSZ

partial def shapesN : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesN k).flatMap fun l =>
          (shapesN (n - k)).map fun r => CartesianShape.node l r

-- sanity: Catalan counts
#eval show IO Unit from do
  IO.println s!"catalan counts 0..8 = {(List.range 9).map (fun n => (shapesN n).length)}"

-- sanity: bpCode really does differ across same-size shapes (anti-vacuity for
-- the whole exercise: if all same-size shapes had the same bpCode, every
-- size-only claim would be vacuous).
#eval show IO Unit from do
  for n in [1,2,3,4,5,6] do
    let ss := shapesN n
    let codes := ss.map (fun s => s.bpCode)
    let distinct := codes.foldl (fun acc c => if acc.contains c then acc else c :: acc) []
    let lens := codes.map (fun c => c.length)
    let distinctLens := lens.foldl (fun acc c => if acc.contains c then acc else c :: acc) []
    IO.println s!"n={n} shapes={ss.length} distinctBpCodes={distinct.length} distinctBpCodeLengths={distinctLens}"

-- F3/F4: the payload lengths.  Do they factor through n?
#eval show IO Unit from do
  for n in [1,2,3,4,5,6,7] do
    let ss := shapesN n
    let sup := ss.map (fun s => builtRelativeSplitBPCloseRankSuperOverhead s)
    let blk := ss.map (fun s => builtRelativeSplitBPCloseRankBlockOverhead s)
    let dsup := sup.foldl (fun acc c => if acc.contains c then acc else c :: acc) []
    let dblk := blk.foldl (fun acc c => if acc.contains c then acc else c :: acc) []
    IO.println s!"n={n} shapes={ss.length} SuperOverhead distinct={dsup.reverse} BlockOverhead distinct={dblk.reverse}"

end AdvSZ
